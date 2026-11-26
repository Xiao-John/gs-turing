"""ledger.py -- the only writer for experiment records, plus the run budget.

Record emission and quota reservation live in one module because they are the
same concern: a read-modify-write cycle on files under one results directory,
serialised by one lock.  Splitting them (as an earlier version did) means two
locks over one piece of state, and the accounting drifts.

Invariants, each of which was established by observing the failure it prevents:

  1. a record is validated BEFORE it is appended, so a malformed record never
     enters the append-only index;
  2. a duplicate case_id is refused by default, because the stored arrays are
     overwritten in place while the jsonl index is append-only -- that mismatch
     has left index entries whose arrays no longer exist;
  3. the run counter is bumped in the SAME locked section as the append, so the
     count cannot drift from the index;
  4. quota is reserved atomically BEFORE work starts, because a per-invocation
     cap does not bound a shared pool: two concurrent batches can each respect
     their own limit and still overrun it together;
  5. settle reconciles planned against ACTUAL usage, and a reservation whose
     holder died or whose TTL elapsed is reclaimed by reap() rather than leaked.

Files, all under the results directory unless overridden:

    cases.jsonl               append-only record index
    ledger.json               run count, per-worker counts, settlements
    ledger_reservations.json  live reservations (kept beside the ledger file)
    .lock                     the one flock guarding every write above
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
import sys
import time
import uuid
from collections import Counter
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parent.parent
RESULTS = REPO / "results"
CASES = RESULTS / "cases.jsonl"
LEDGER = RESULTS / "ledger.json"
RESERVATIONS = LEDGER.parent / f"{LEDGER.stem}_reservations.json"
LOCK = RESULTS / ".lock"

DEFAULT_LIMIT = 200
DEFAULT_TTL = 3600

# Process-local limit override; None means "use the ledger file's limit, then
# DEFAULT_LIMIT".  Kept separate from DEFAULT_LIMIT so an override is reversible
# without rewriting the on-disk budget.
_LIMIT: int | None = None

if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))
from experiment.validate import load_records, validate_record  # noqa: E402


# ---------------------------------------------------------------------------
# Layout
# ---------------------------------------------------------------------------
def set_results_dir(path: str | Path, ledger_path: str | Path | None = None,
                    cases_path: str | Path | None = None) -> None:
    """Re-point every path this module writes to.

    The default layout is ``path/{cases.jsonl,ledger.json,.lock}``; explicit
    ``ledger_path``/``cases_path`` let one budget serve several case indexes.
    Reservations follow the LEDGER file, never the results directory, so a
    budget and its quota can never end up in different places.
    """
    global RESULTS, CASES, LEDGER, RESERVATIONS, LOCK
    RESULTS = Path(path)
    RESULTS.mkdir(parents=True, exist_ok=True)
    LEDGER = Path(ledger_path) if ledger_path is not None else RESULTS / "ledger.json"
    CASES = Path(cases_path) if cases_path is not None else RESULTS / "cases.jsonl"
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    CASES.parent.mkdir(parents=True, exist_ok=True)
    RESERVATIONS = LEDGER.parent / f"{LEDGER.stem}_reservations.json"
    LOCK = RESULTS / ".lock"


def set_limit(n: int | None) -> None:
    """Override the process-wide run limit.  ``None`` restores the default."""
    global _LIMIT
    if n is not None and int(n) <= 0:
        raise ValueError("limit must be positive or None")
    _LIMIT = None if n is None else int(n)


# ---------------------------------------------------------------------------
# Small file helpers
# ---------------------------------------------------------------------------
def _load(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return default


def _save(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False, default=str),
                    encoding="utf-8")


def _ledger_dict() -> dict:
    return _load(LEDGER, {"runs": 0, "per_worker": {}, "settlements": []})


def _reservations() -> dict:
    return _load(RESERVATIONS, {})


def _held(resv: dict) -> int:
    return sum(int(v.get("n", 0)) for v in resv.values())


def _effective_limit() -> int:
    if _LIMIT is not None:
        return _LIMIT
    return int(_ledger_dict().get("limit") or DEFAULT_LIMIT)


def _expired(rec: dict, now: float) -> bool:
    """A reservation is stale when its TTL elapsed or its holder is gone."""
    ttl = rec.get("ttl") or 0
    if ttl and rec.get("t0") and now - float(rec["t0"]) > float(ttl):
        return True
    pid = rec.get("pid")
    if pid:
        try:
            os.kill(int(pid), 0)
        except OSError:
            return True
    return False


# ---------------------------------------------------------------------------
# Cases
# ---------------------------------------------------------------------------
def load_cases() -> list[dict]:
    """Every record currently in the index, in append order."""
    return load_records(CASES)


def already_done(case_id: str) -> bool:
    """True iff a *completed* record with this id exists.  A failed attempt does
    not count as done, so it can be retried under a new id."""
    return any(r.get("case_id") == case_id and r.get("status") == "completed"
               for r in load_cases())


def _bump_locked(n: int, worker: str) -> dict:
    """Caller already holds the lock.  Never call this on its own."""
    b = _ledger_dict()
    b.setdefault("limit", _effective_limit())
    b["runs"] = int(b.get("runs", 0)) + int(n)
    pw = b.setdefault("per_worker", {})
    w = worker or "unknown"
    pw[w] = int(pw.get(w, 0)) + int(n)
    _save(LEDGER, b)
    return b


def append_case(rec: dict, results_dir: str | Path | None = None,
                allow_overwrite: bool = False) -> dict:
    """Validate, append, and account for one record -- atomically.

    Validation happens before the lock is taken, so an invalid record costs
    nothing and can never enter the append-only index.  The counter moves inside
    the same locked section as the append, so the count and the index cannot
    disagree even under concurrent writers.

    ``allow_overwrite`` is the deliberate supersede path: use it only when a case
    is knowingly being replaced, because a plain repeat of a completed case_id
    means the stored arrays were rewritten while the older index entry stays.

    Returns a summary dict: case_id, worker, runs, per_worker, cases path.
    """
    errs = validate_record(rec)
    if errs:
        raise ValueError(f"record for {rec.get('case_id')} violates schema.json: "
                         + "; ".join(errs[:4]))
    if results_dir is not None:
        set_results_dir(results_dir)

    cid = rec.get("case_id")
    worker = rec.get("worker") or "unknown"
    line = json.dumps(rec, default=str, ensure_ascii=False)

    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            prev_status = None
            for r in load_cases():
                if r.get("case_id") == cid:
                    prev_status = r.get("status")
            if prev_status is not None and not allow_overwrite:
                if prev_status == "failed":
                    raise RuntimeError(
                        f"case_id {cid!r} exists as a FAILED run. It is safe to "
                        f"retry: use a new case_id (the failed record stays in the "
                        f"index for the audit trail), or pass allow_overwrite=True "
                        f"to supersede it deliberately.")
                raise RuntimeError(
                    f"case_id {cid!r} already exists. The stored arrays would be "
                    f"overwritten while this index is append-only, leaving a stale "
                    f"record that no longer matches any file. Choose a new case_id, "
                    f"or pass allow_overwrite=True to supersede deliberately.")
            CASES.parent.mkdir(parents=True, exist_ok=True)
            with CASES.open("a", encoding="utf-8") as fh:
                fh.write(line + "\n")
            b = _bump_locked(1, worker)
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)
    return {"case_id": cid, "worker": worker, "runs": int(b.get("runs", 0)),
            "per_worker": b.get("per_worker", {}), "cases": str(CASES)}


# ---------------------------------------------------------------------------
# Budget
# ---------------------------------------------------------------------------
def budget_state() -> dict:
    """The charged side of the budget: settled runs and their attribution."""
    b = _ledger_dict()
    return {"runs": int(b.get("runs", 0)), "per_worker": b.get("per_worker", {})}


def bump(n: int = 1, worker: str = "core") -> dict:
    """Charge n runs to worker without writing a record.

    Only for work that never produces a record (aborted preparation, replay of
    an existing trajectory).  append_case() bumps for itself, inside its own
    lock, so calling both for one run would double-charge.
    """
    if int(n) < 0:
        raise ValueError("n must be non-negative")
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            _bump_locked(int(n), worker)
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)
    return budget_state()


def runs_left(limit: int) -> int:
    """Slots still available against ``limit``, counting live reservations."""
    return max(0, int(limit) - budget_state()["runs"] - _held(_reservations()))


# ---------------------------------------------------------------------------
# Quota
# ---------------------------------------------------------------------------
def reserve(n: int, purpose: str = "", batch_id: str | None = None,
            ttl: float = DEFAULT_TTL) -> str:
    """Atomically take ``n`` slots and return a reservation id.

    The check and the take share one lock, so two concurrent batches cannot each
    pass their own cap check and jointly overrun the shared pool.  Raises
    RuntimeError rather than degrading: running without a reservation defeats the
    point.  ``ttl`` (seconds, <=0 disables) is the lease that lets a crashed
    holder's slots come back.
    """
    if int(n) <= 0:
        raise ValueError("n must be positive")
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            resv = _reservations()
            now = time.time()
            # Reclaim expired leases here as well as in reap(), so a stale
            # reservation cannot silently block new work.
            for k in [k for k, v in resv.items() if _expired(v, now)]:
                resv[k]["n"] = 0
                resv[k]["reclaimed"] = time.strftime("%F %T")
            limit = _effective_limit()
            runs = budget_state()["runs"]
            avail = limit - runs - _held(resv)
            if int(n) > avail:
                raise RuntimeError(
                    f"REFUSING to reserve {n} for {batch_id or purpose or 'batch'!r}: "
                    f"only {avail} slot(s) available (limit {limit}, spent {runs}, "
                    f"held by other reservations {_held(resv)}). "
                    f"Shrink the batch or settle a finished one.")
            rid = uuid.uuid4().hex[:12]
            while rid in resv:  # never shadow a live reservation
                rid = uuid.uuid4().hex[:12]
            resv[rid] = {"n": int(n), "purpose": purpose, "batch_id": batch_id,
                         "pid": os.getpid(), "t0": now, "ttl": ttl,
                         "at": time.strftime("%F %T")}
            _save(RESERVATIONS, resv)
            return rid
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)


def settle(reservation_id: str, actual: int | None = None) -> None:
    """Release a reservation, recording planned vs actual usage.

    ``actual`` is the honest number of runs performed; it is recorded for
    reconciliation but does NOT increment the run counter, because each run's
    cost is already charged by append_case()/bump().  Charging here too would
    double-count every successful run.  Settling is idempotent by construction:
    the reservation is removed, so a second settle finds nothing to release.
    """
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            resv = _reservations()
            r = resv.pop(reservation_id, None)
            if r is None:
                raise RuntimeError(f"no reservation for {reservation_id!r}")
            b = _ledger_dict()
            done = b.setdefault("settlements", [])
            if not any(x.get("reservation_id") == reservation_id for x in done):
                done.append({"reservation_id": reservation_id,
                             "batch_id": r.get("batch_id"),
                             "reserved": r.get("n"),
                             "actual": None if actual is None else int(actual),
                             "at": time.strftime("%F %T")})
                _save(LEDGER, b)
            _save(RESERVATIONS, resv)
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)


def reap() -> list[str]:
    """Drop reservations whose TTL elapsed or whose holder is gone; return ids.

    Without this, a crashed controller permanently removes its slots from the
    pool: the budget is conservative (it never refunds by itself), so reclamation
    has to be explicit and reported.
    """
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    dropped: list[str] = []
    with LOCK.open("a+") as h:
        fcntl.flock(h, fcntl.LOCK_EX)
        try:
            resv = _reservations()
            now = time.time()
            for k in [k for k, v in resv.items()
                      if v.get("n") and _expired(v, now)]:
                resv.pop(k, None)
                dropped.append(k)
            if dropped:
                _save(RESERVATIONS, resv)
        finally:
            fcntl.flock(h, fcntl.LOCK_UN)
    return dropped


def status() -> dict:
    """Read-only view of budget, live reservations, and what is still usable."""
    runs = budget_state()["runs"]
    limit = _effective_limit()
    resv = _reservations()
    held = _held(resv)
    return {"runs": runs, "limit": limit, "reserved": held,
            "remaining": limit - runs - held,
            "active": {k: v for k, v in resv.items() if v.get("n")}}


def audit() -> dict:
    """Reconcile the append-only index against the ledger's run counter.

    The counter is bumped only by append_case()/bump(), so in a healthy tree the
    record count and the charged count agree; a non-zero delta means records were
    written around this module or the ledger was edited by hand.
    """
    recs = load_cases()
    cnt = Counter(r.get("case_id") for r in recs)
    dup = {k: v for k, v in cnt.items() if v > 1}
    runs = budget_state()["runs"]
    return {"records": len(recs), "unique": len(cnt), "ledger_runs": runs,
            "delta": len(recs) - runs, "reconciled": len(recs) == runs,
            "duplicates": dup,
            "extra_records": sum(v - 1 for v in dup.values())}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Record ledger: budget status and quota reservations.")
    ap.add_argument("command", nargs="?", default="all",
                    choices=["all", "status", "reap", "audit"],
                    help="all = status + audit (default)")
    args = ap.parse_args(argv)

    if args.command == "reap":
        print(json.dumps({"reaped": reap(), "status": status()}, indent=2,
                         ensure_ascii=False))
    elif args.command == "status":
        print(json.dumps(status(), indent=2, ensure_ascii=False))
    elif args.command == "audit":
        print(json.dumps(audit(), indent=2, ensure_ascii=False))
    else:
        print(json.dumps({"status": status(), "audit": audit()}, indent=2,
                         ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
