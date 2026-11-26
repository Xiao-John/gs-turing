"""Recompute stored metrics and cross-check them against the recorded claims.

A ledger record is a *claim* about a run; the ``.npz`` beside it is the evidence.
Scalars are cheap to re-derive from the arrays, so this module re-derives them
with :func:`core.gs.metrics` and reports every disagreement instead of trusting
the record.  That invariant matters because a record can silently go stale: the
ledger is append-only while ``results/<case_id>.npz`` is overwritten, so an
earlier line for a repeated ``case_id`` can describe a state that no longer
exists.  A disagreement found here is worth more than a disagreement found after
the arrays have been deleted.

No simulation is run.  :func:`core.gs.metrics` reads only ``u``, ``v``,
``ures_now``, ``t``, ``n`` and ``h``, so stored arrays are wrapped in a small
stand-in object (:class:`_StoredState`) rather than reimplementing the metrics --
a second implementation would inevitably drift from the solver's.

Entry points
------------
``recompute(rec)``          stored arrays -> :func:`core.gs.metrics` dict
``crosscheck(rec, npz)``    compare those against ``rec["final_metrics"]``
``audit()``                 whole-ledger sweep: cross-checks, stale, orphan, dup
``main(argv)``              CLI (see ``--help``)
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import numbers
import os
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import numpy as np

REPO = Path(__file__).resolve().parent.parent
if str(REPO) not in sys.path:          # so ``core`` resolves when run as a script
    sys.path.insert(0, str(REPO))

from core import gs                                             # noqa: E402

CASES_NAME = "cases.jsonl"
DEFAULT_THRESHOLD = 0.05

# Why a tolerance at all, and why this one:
# the arrays are written from the same float64 fields the record was measured on,
# so an honest record reproduces to a few ulps; a float32 round-trip through a
# frame stack costs at most ~1e-7 relative.  A stale or overwritten record
# disagrees by an O(1) fraction.  The window therefore separates round-off from
# real staleness with many orders of magnitude to spare.
RTOL = 1e-6
ATOL = 1e-9
# Integer-valued counts must agree exactly; a near-miss component count is a
# different topology, not round-off.
EXACT_METRICS = frozenset({"components", "active_area_cells"})

# Column order of metrics_table.csv: the keys core.gs.metrics emits, in a fixed
# order so the table can be diffed between runs without sorting heuristics.
METRIC_ORDER: tuple[str, ...] = (
    "t", "Mv", "vmax", "vmin", "umin", "umax",
    "active_area_cells", "active_area", "threshold", "reaction_flux",
    "resource_target_mean", "resource_target_min", "resource_target_max",
    "cy", "cx", "Rg", "elongation", "components",
)

# Identity columns, then one recomputed column per metric.  "centroid" is the
# (cy, cx) pair and is represented by its components to keep the table scalar.
CSV_ID_COLUMNS: tuple[str, ...] = (
    "case_id", "worker", "status", "method", "n", "h", "dt", "t_final",
    "npz_path", "arrays_available", "duplicate", "cross_check", "n_findings",
    "findings",
)
CSV_COLUMNS: tuple[str, ...] = CSV_ID_COLUMNS + tuple(
    f"recomputed_{m}" for m in METRIC_ORDER)


# ------------------------------------------------------------------- locations
def results_dir() -> Path:
    """The results root, resolved without hardcoding a path.

    Precedence: ``$GS_RESULTS_DIR`` (test/alternate root), then the ledger's own
    ``RESULTS`` when :mod:`experiment.ledger` has been imported and possibly
    redirected, then ``REPO/results``.  Consulting the ledger keeps analysis on
    whichever directory the runner actually wrote to.
    """
    env = os.environ.get("GS_RESULTS_DIR")
    if env:
        return Path(env).expanduser().resolve()
    try:
        from experiment import ledger as _ledger        # type: ignore
        root = getattr(_ledger, "RESULTS", None)
        if root is not None:
            return Path(root)
    except Exception:
        pass
    return REPO / "results"


def cases_path(root: Path | str | None = None) -> Path:
    """Path of the JSONL ledger under ``root`` (default: :func:`results_dir`)."""
    return (Path(root) if root is not None else results_dir()) / CASES_NAME


def load_cases(root: Path | str | None = None,
               malformed: list[int] | None = None) -> list[dict]:
    """Read the JSONL ledger in directory ``root`` (default: :func:`results_dir`).

    A blank line is ignored.  An unparseable line is skipped, but its 1-based
    line number is appended to ``malformed`` when a list is supplied, so the
    caller can report the loss instead of quietly shrinking the index.
    """
    path = cases_path(root)
    if not path.exists():
        return []
    records: list[dict] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            if malformed is not None:
                malformed.append(lineno)
            continue
        if isinstance(obj, dict):
            records.append(obj)
        elif malformed is not None:
            malformed.append(lineno)
    return records


def npz_path_for(rec: Mapping[str, Any], root: Path | str | None = None) -> Path:
    """Resolve a record's arrays.

    ``npz_path`` is honoured as written (absolute) or tried against both the repo
    root and the results root (relative records predate any single convention).
    Without it, the conventional ``<root>/<case_id>.npz`` is assumed.  A
    non-existent candidate is still returned, so the caller can report *which*
    path was missing rather than a bare "not found".
    """
    base = Path(root) if root is not None else results_dir()
    raw = rec.get("npz_path")
    if raw:
        p = Path(str(raw))
        if p.is_absolute():
            return p
        for cand in (REPO / p, base / p):
            if cand.exists():
                return cand
        return REPO / p
    return base / f"{rec.get('case_id')}.npz"


# --------------------------------------------------------------- stored state
@dataclass
class _StoredState:
    """The subset of :class:`core.gs.FieldSolver` that :func:`gs.metrics` reads.

    Rebuilding just these attributes is what lets stored arrays be measured
    without instantiating a solver or advancing time.
    """

    u: np.ndarray
    v: np.ndarray
    ures_now: np.ndarray
    t: float
    n: int
    h: float

    @property
    def ny(self) -> int:
        return int(self.u.shape[0])

    @property
    def nx(self) -> int:
        return int(self.u.shape[1])


def _open_npz(obj: Any) -> Any:
    """Accept a path or an already-open archive/mapping; return an npz-like."""
    if isinstance(obj, (str, Path)):
        return np.load(Path(obj))
    if hasattr(obj, "__getitem__") and hasattr(obj, "__contains__"):
        return obj
    raise TypeError(f"cannot read arrays from {type(obj).__name__}")


def _has(z: Any, key: str) -> bool:
    try:
        return key in z
    except TypeError:
        return False


def _field(z: Any, key: str, default: float) -> float:
    if not _has(z, key):
        return float(default)
    try:
        return float(np.asarray(z[key]).reshape(-1)[0])
    except (TypeError, ValueError):
        return float(default)


def _state_from_npz(z: Any, rec: Mapping[str, Any]) -> _StoredState:
    """Wrap the stored end state as the stand-in :func:`gs.metrics` consumes.

    ``h``/``t``/``n`` come from the archive and fall back to the record, but the
    arrays themselves never do: they are the evidence being checked.  A missing
    ``ures`` becomes a uniform placeholder and the caller refuses to score the
    resource metrics, because inventing a driver and then flagging it would be a
    false finding.
    """
    u = np.asarray(z["u"], dtype=np.float64)
    v = np.asarray(z["v"], dtype=np.float64)
    if u.shape != v.shape or u.ndim != 2:
        raise ValueError(f"stored u/v shapes {u.shape}/{v.shape} are not a 2-D pair")
    # `n` stays the row count for backward compatibility with square archives;
    # nx/ny come from the arrays, which are the evidence.
    n = int(u.shape[0])
    h = _field(z, "h", float(rec.get("h") or 1.0))
    t = _field(z, "t", float(rec.get("t_final") or 0.0))
    ures = (np.asarray(z["ures"], dtype=np.float64) if _has(z, "ures")
            else np.ones_like(u))
    if ures.shape != u.shape:
        raise ValueError(f"stored ures shape {ures.shape} != u shape {u.shape}")
    return _StoredState(u=u, v=v, ures_now=ures, t=t, n=n, h=h)


def _declared_threshold(rec: Mapping[str, Any]) -> float:
    """The threshold the record says it measured at, so the check re-measures
    under the same convention rather than silently changing it."""
    fm = rec.get("final_metrics")
    raw = fm.get("threshold") if isinstance(fm, Mapping) else None
    if isinstance(raw, bool) or not isinstance(raw, (int, float)):
        return DEFAULT_THRESHOLD
    return float(raw)


# ------------------------------------------------------------------- recompute
def recompute(rec: Mapping[str, Any], npz: Any | None = None) -> dict:
    """Recompute the scalar metrics of ``rec`` from its stored arrays.

    ``npz`` may be a path, an open :class:`numpy.lib.npyio.NpzFile`, or any
    mapping; ``None`` resolves the path from the record.  Returns the dict from
    :func:`core.gs.metrics`, including ``centroid``.
    """
    z = _open_npz(npz) if npz is not None else _open_npz(npz_path_for(rec))
    state = _state_from_npz(z, rec)
    return gs.metrics(state, thr=_declared_threshold(rec))


def _disagrees(metric: str, recomputed: Any, claimed: Any) -> bool:
    """Whether a recomputed scalar fails to reproduce the claimed one.

    ``None`` is a legitimate value for shape metrics of an extinct state, so
    ``None == None`` is a match and ``None`` versus a number is not.
    """
    if recomputed is None and claimed is None:
        return False
    if recomputed is None or claimed is None:
        return True
    try:
        a, b = float(recomputed), float(claimed)
    except (TypeError, ValueError):
        return True
    if metric in EXACT_METRICS:
        return int(round(a)) != int(round(b))
    if math.isnan(a) and math.isnan(b):
        return False
    if not (math.isfinite(a) and math.isfinite(b)):
        return a != b
    return abs(a - b) > ATOL + RTOL * max(abs(a), abs(b))


def _jsonable(value: Any) -> Any:
    """Tuples/arrays become lists and numpy scalars plain numbers, so a finding
    survives ``json.dumps`` and is readable in the CSV."""
    if value is None or isinstance(value, (bool, str)):
        return value
    if isinstance(value, numbers.Number):
        f = float(value)
        return f if math.isfinite(f) else None
    try:
        seq = list(value)
    except TypeError:
        return str(value)
    return [_jsonable(x) for x in seq]


def crosscheck(rec: Mapping[str, Any], npz: Any) -> list[dict]:
    """Compare recomputed metrics with the record's claims.

    Returns one finding per disagreeing metric, each
    ``{case_id, metric, claimed, recomputed, delta}`` where ``delta`` is
    ``recomputed - claimed`` (``None`` when either side is missing).  An empty
    list means every claim the record made is reproduced by its arrays; an empty
    list is *not* an endorsement of metrics the record never claimed.
    """
    z = _open_npz(npz)
    measured = recompute(rec, z)
    fm = rec.get("final_metrics")
    claimed: Mapping[str, Any] = fm if isinstance(fm, Mapping) else {}
    has_ures = _has(z, "ures")

    findings: list[dict] = []
    for metric in METRIC_ORDER:
        if metric not in claimed or metric not in measured:
            continue
        if metric.startswith("resource_target") and not has_ures:
            # no driver was stored, so the resource claims are unscorable
            continue
        got, want = measured[metric], claimed[metric]
        if not _disagrees(metric, got, want):
            continue
        try:
            delta: float | None = float(got) - float(want)
        except (TypeError, ValueError):
            delta = None
        findings.append({
            "case_id": rec.get("case_id"),
            "metric": metric,
            "claimed": _jsonable(want),
            "recomputed": _jsonable(got),
            "delta": delta,
        })
    return findings


# ----------------------------------------------------------------------- audit
def _base_row(rec: Mapping[str, Any], path: Path, duplicate: bool) -> dict:
    return {
        "case_id": rec.get("case_id"),
        "worker": rec.get("worker"),
        "status": rec.get("status"),
        "method": rec.get("method"),
        "n": rec.get("n"),
        "h": rec.get("h"),
        "dt": rec.get("dt"),
        "t_final": rec.get("t_final"),
        "npz_path": str(path),
        "arrays_available": False,
        "duplicate": duplicate,
        "cross_check": "unscored",
        "n_findings": 0,
        "findings": "",
    }


def _finding_text(findings: list[dict]) -> str:
    return "; ".join(
        f"{f['metric']}:{f['claimed']}->{f['recomputed']}" for f in findings)


def audit(filter_substr: str | None = None, limit: int | None = None,
          root: Path | str | None = None) -> dict:
    """Sweep the ledger and report every integrity problem it contains.

    Detects four distinct things, deliberately not collapsed into one number:

    * a **mismatch** -- arrays that do not reproduce the record's own claims;
    * a **stale record** -- a record whose arrays are missing on disk;
    * an **orphan** -- an ``.npz`` with no record naming it;
    * a **duplicate** ``case_id`` -- an append-only ledger cannot have two
      authoritative lines for one case, and the arrays can only match one.

    ``filter_substr``/``limit`` narrow the records (and the orphan scan, by
    filename, so a filtered audit does not report every other case as an orphan).
    ``root`` overrides :func:`results_dir` for tests.
    """
    base = Path(root) if root is not None else results_dir()
    malformed: list[int] = []
    records = load_cases(base, malformed=malformed)
    if filter_substr:
        records = [r for r in records
                   if filter_substr in str(r.get("case_id") or "")]
    if limit is not None:
        records = records[:max(0, int(limit))]

    counts = Counter(str(r.get("case_id")) for r in records if r.get("case_id"))
    duplicates = {cid: n for cid, n in counts.items() if n > 1}

    rows: list[dict] = []
    findings: list[dict] = []
    missing_npz: list[str] = []
    errored: list[str] = []
    referenced: set[Path] = set()

    for rec in records:
        cid = str(rec.get("case_id"))
        path = npz_path_for(rec, base)
        row = _base_row(rec, path, duplicate=counts.get(cid, 1) > 1)
        if not path.exists():
            row["cross_check"] = "missing_arrays"
            missing_npz.append(cid or f"<line {len(rows)}>")
            rows.append(row)
            continue
        referenced.add(path.resolve())
        try:
            with np.load(path) as z:
                measured = recompute(rec, z)
                found = crosscheck(rec, z)
                claimed_any = bool(isinstance(rec.get("final_metrics"), Mapping)
                                   and rec["final_metrics"])
        except Exception as exc:                      # noqa: BLE001 - reported
            # A corrupt or non-conforming archive is a finding in itself; it must
            # not abort the sweep and hide the remaining cases.
            row["cross_check"] = "error"
            row["findings"] = f"{type(exc).__name__}: {exc}"
            errored.append(cid or path.name)
            rows.append(row)
            continue

        row["arrays_available"] = True
        for metric in METRIC_ORDER:
            row[f"recomputed_{metric}"] = measured.get(metric)
        row["n_findings"] = len(found)
        row["findings"] = _finding_text(found)
        if found:
            row["cross_check"] = "mismatch"
        elif claimed_any:
            row["cross_check"] = "match"
        else:
            row["cross_check"] = "no_claim"
        findings.extend(found)
        rows.append(row)

    pattern = f"*{filter_substr}*.npz" if filter_substr else "*.npz"
    orphans = sorted(
        p.name for p in base.glob(pattern)
        if not p.name.startswith(".") and p.resolve() not in referenced)

    def _count(state: str) -> int:
        return sum(1 for r in rows if r["cross_check"] == state)

    return {
        "results_dir": str(base),
        "n_records": len(records),
        "n_unique_cases": len(counts),
        "n_arrays_available": sum(1 for r in rows if r["arrays_available"]),
        "n_matched": _count("match"),
        "n_mismatched": _count("mismatch"),
        "n_no_claim": _count("no_claim"),
        "n_unscored": _count("unscored"),
        "missing_npz": missing_npz,
        "n_missing_npz": len(missing_npz),
        "errored": errored,
        "n_errored": len(errored),
        "orphans": orphans,
        "n_orphans": len(orphans),
        "duplicates": duplicates,
        "n_duplicate_cases": len(duplicates),
        "malformed_lines": malformed,
        "findings": findings,
        "n_findings": len(findings),
        "rows": rows,
    }


# ------------------------------------------------------------------- reporting
def write_csv(path: Path | str, rows: list[dict]) -> Path:
    """Write ``rows`` with the frozen column order in :data:`CSV_COLUMNS`."""
    out = Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(CSV_COLUMNS),
                                extrasaction="ignore", restval="")
        writer.writeheader()
        writer.writerows(rows)
    return out


def _print_report(report: Mapping[str, Any], csv_out: Path | None) -> None:
    print(f"analyze: {report['n_records']} records "
          f"({report['n_unique_cases']} unique case_ids) in {report['results_dir']}")
    print(f"  arrays available : {report['n_arrays_available']}/{report['n_records']}")
    print(f"  cross-check      : match {report['n_matched']}   "
          f"mismatch {report['n_mismatched']}   "
          f"no_claim {report['n_no_claim']}   "
          f"unscored {report['n_unscored']}")
    print(f"  stale (no arrays): {report['n_missing_npz']}   "
          f"unreadable: {report['n_errored']}   "
          f"orphan npz: {report['n_orphans']}   "
          f"duplicate case_ids: {report['n_duplicate_cases']}")
    if report["malformed_lines"]:
        print(f"  malformed ledger lines: {report['malformed_lines'][:10]}"
              f"{' ...' if len(report['malformed_lines']) > 10 else ''}")
    if report["orphans"]:
        print(f"  orphans: {report['orphans'][:8]}"
              f"{' ...' if len(report['orphans']) > 8 else ''}")
    if report["duplicates"]:
        shown = list(report["duplicates"].items())[:8]
        print(f"  duplicate case_ids: {shown}"
              f"{' ...' if len(report['duplicates']) > 8 else ''}")
    if report["missing_npz"]:
        print(f"  records without arrays: {report['missing_npz'][:8]}"
              f"{' ...' if len(report['missing_npz']) > 8 else ''}")
    for finding in report["findings"][:12]:
        print(f"    MISMATCH {finding['case_id']} {finding['metric']}: "
              f"claimed={finding['claimed']} recomputed={finding['recomputed']} "
              f"delta={finding['delta']}")
    if len(report["findings"]) > 12:
        print(f"    ... {len(report['findings']) - 12} more findings")
    if csv_out is not None:
        print(f"  -> {csv_out}")


def main(argv: list[str] | None = None) -> int:
    """CLI.  Returns 0 unless ``--strict`` is set and a mismatch was found.

    ``--strict`` gates on recompute-vs-record mismatches only: stale, orphan and
    duplicate records are always printed, but they describe the ledger's shape
    rather than a contradiction with the stored arrays.
    """
    ap = argparse.ArgumentParser(
        prog="python -m experiment.analyze",
        description="Recompute stored metrics and cross-check them against the "
                    "ledger record.")
    ap.add_argument("--filter", default=None, metavar="SUBSTR",
                    help="only records whose case_id contains SUBSTR")
    ap.add_argument("--limit", type=int, default=None, metavar="N",
                    help="analyse at most N records after filtering")
    ap.add_argument("--csv", default=None, metavar="PATH",
                    help="metrics table destination "
                         "(default: <results>/metrics_table.csv)")
    ap.add_argument("--strict", action="store_true",
                    help="exit non-zero when any cross-check mismatch is found")
    args = ap.parse_args(argv)

    root = results_dir()
    csv_out = Path(args.csv) if args.csv else root / "metrics_table.csv"
    report = audit(args.filter, args.limit, root=root)
    write_csv(csv_out, report["rows"])
    _print_report(report, csv_out)

    if args.strict and report["n_mismatched"]:
        print(f"analyze: --strict: {report['n_findings']} finding(s) in "
              f"{report['n_mismatched']} record(s)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
