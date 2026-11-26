"""Declarative batch runner.

A *spec* is a JSON list of case objects (or ``{"cases": [...]}``).  The runner
turns each one into a solved trajectory, writes the end state to
``results/<case_id>.npz`` and appends one validated record to the ledger.  Case
ids already present in the ledger are skipped, so replaying a spec costs nothing
and a crashed batch can simply be re-run.

Why a declarative runner
------------------------
Writing a bespoke sweep script per question is how an experiment set ends up with
several incompatible record shapes and several private notions of "done".  The
spec is the only place a configuration is declared; accounting, idempotence,
saving and validation live here once.

Spec fields
-----------
Identity / bookkeeping
    ``case_id`` (required), ``worker``, ``note``, ``tags``, ``parent_id``

Grid and model
    ``n``, ``h``, ``dt``, ``Du``, ``Dv``, ``f``, ``k`` (defaults 192, 1, 1,
    0.16, 0.08, 0.038, 0.068)

Integration
    ``method`` (``euler`` | ``imex``), ``spectral_lap``, ``dealias``,
    ``every`` (sample interval in steps), ``keep_frames``

Initial condition — one of
    ``init="uniform"``  u=1, v=0 everywhere (plus optional ``blobs``)
    ``init="blobs"``    u=1, v=0 with the listed v blobs (same as uniform+blobs)
    ``init="npz"``      load ``u``/``v`` from ``parent_npz`` or from the stored
                        result of case ``parent``
    ``blobs``           list of ``{cy, cx, radius, v, u?, shape?}``; ``u``
                        defaults to 1.0 (no depletion); ``shape`` is ``disk``
                        (default) or ``square``

Driver
    ``resource``        ``{"kind": ..., ...}``, see :func:`build_resource`

Preparation (applied to the initial condition, then re-recorded as t=0)
    ``prep``            ``{"scale_v": s, "shift_u": {"dy": d, "dx": d},
                        "shift_v": {...}, "reset_u_to": x, "reset_v_to": x,
                        "wait": t}``

Run
    ``T`` (model time to reach) or ``observe`` (alias), ``f_switch``
    (``[[t, f], ...]`` applied in order)

Pinned cells
    ``fixed_patch``     ``{"rows": [r0, r1], "cols": [c0, c1]}`` held at u=1, v=0
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parent.parent
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from core import gs                                        # noqa: E402
from experiment import ledger                              # noqa: E402


# --------------------------------------------------------------- resource builder
def build_resource(spec: dict, n: int, h: float) -> gs.ResourceField:
    """Turn a spec's ``resource`` block into a :class:`core.gs.ResourceField`."""
    r = spec.get("resource") or {"kind": "uniform"}
    kind = r.get("kind", "uniform")
    if kind == "uniform":
        return gs.uniform(r.get("value", 1.0))
    if kind == "sine_gradient":
        return gs.sine_gradient(n, h, A=r["A"],
                                wavelength=r.get("wavelength", n * h),
                                base=r.get("base", 1.0), axis=r.get("axis", "x"))
    if kind == "tanh_gradient":
        return gs.tanh_gradient(n, h, A=r["A"], xc=r.get("xc", n / 2), ell=r["ell"],
                                base=r.get("base", 1.0), axis=r.get("axis", "x"))
    if kind == "periodic_moving_band":
        return gs.periodic_gaussian_band(n, h, xs0=r["xs0"], vband=r["vband"],
                                         w=r["w"], base=r.get("base", 1.0),
                                         A=r.get("A", 0.3), axis=r.get("axis", "x"))
    if kind == "array":
        # A designed static field, read from an npz.  This is the hook for
        # deliberately structured supply landscapes.
        z = np.load(r["path"])
        a = z[r.get("key", "ures")].astype(float)
        if a.shape != (n, n):
            raise ValueError(f"resource array {r['path']} has shape {a.shape}, "
                             f"expected {(n, n)}")
        return gs.from_array(a, kind=r.get("label", "array"))
    raise ValueError(f"unknown resource kind {kind!r}")


# ------------------------------------------------------------------ initial states
def blob_mask(n: int, cy: float, cx: float, radius: float,
              shape: str = "disk") -> np.ndarray:
    """Boolean mask of a centred disk or square, clipped to the domain."""
    yy, xx = np.indices((n, n))
    if shape == "disk":
        return (yy - cy) ** 2 + (xx - cx) ** 2 <= radius ** 2
    if shape == "square":
        r = int(round(radius))
        m = np.zeros((n, n), bool)
        y0, y1 = max(0, int(cy) - r), min(n, int(cy) + r + 1)
        x0, x1 = max(0, int(cx) - r), min(n, int(cx) + r + 1)
        m[y0:y1, x0:x1] = True
        return m
    raise ValueError(f"unknown blob shape {shape!r}")


def build_initial(spec: dict, n: int) -> tuple[np.ndarray, np.ndarray]:
    """Return ``(u, v)`` for the requested initial condition."""
    init = spec.get("init", "uniform" if not spec.get("blobs") else "blobs")
    if init == "npz":
        path = spec.get("parent_npz")
        if path is None and spec.get("parent"):
            path = ledger.RESULTS / f"{spec['parent']}.npz"
        if path is None:
            raise ValueError("init='npz' needs 'parent_npz' or 'parent'")
        z = np.load(path)
        u = z["u"].astype(float)
        v = z["v"].astype(float)
        if u.shape != (n, n):
            raise ValueError(f"parent field {path} has shape {u.shape}, "
                             f"spec says n={n}")
        return u, v
    if init in ("uniform", "blobs"):
        u = np.ones((n, n))
        v = np.zeros((n, n))
        for b in spec.get("blobs", []):
            m = blob_mask(n, b["cy"], b["cx"], b["radius"], b.get("shape", "disk"))
            if b.get("u") is not None:
                u[m] = float(b["u"])
            v[m] = float(b["v"])
        return u, v
    raise ValueError(f"unknown init {init!r}")


def fixed_mask_from_spec(spec: dict, n: int) -> np.ndarray | None:
    fp = spec.get("fixed_patch")
    if not fp:
        return None
    m = np.zeros((n, n), np.uint8)
    (r0, r1), (c0, c1) = fp["rows"], fp["cols"]
    m[r0:r1, c0:c1] = 1
    return m


# ------------------------------------------------------------------------ one case
def run_one(spec: dict, results_dir: Path | None = None, dry: bool = False) -> dict:
    """Solve one case, save its end state and append its record.

    Raises on a malformed spec; returns a dict with ``skipped`` when the case is
    already in the ledger.
    """
    results_dir = Path(results_dir) if results_dir else ledger.RESULTS
    cid = spec["case_id"]
    if ledger.already_done(cid):
        return {"case_id": cid, "skipped": True}

    n = int(spec["n"])
    h = float(spec.get("h", 1.0))
    dt = float(spec.get("dt", 1.0))
    res = build_resource(spec, n, h)
    u, v = build_initial(spec, n)
    if dry:
        return {"case_id": cid, "dry": True, "n": n, "resource": res.describe()}

    prep = dict(spec.get("prep") or {})
    # `wait` runs the model before the state is recorded, so it is preparation.
    needs_prep = any(prep.get(k) is not None
                     for k in ("scale_v", "shift_u", "shift_v",
                               "reset_u_to", "reset_v_to", "wait"))

    s = gs.FieldSolver(
        n=n, h=h, dt=dt, Du=spec.get("Du", 0.16), Dv=spec.get("Dv", 0.08),
        f=float(spec["f"]), k=float(spec["k"]), u=u, v=v, resource=res,
        method=spec.get("method", "euler"),
        spectral_lap=spec.get("spectral_lap", False),
        dealias=spec.get("dealias", False),
        every=int(spec.get("every", 500)),
        keep_frames=bool(spec.get("keep_frames", False)),
        fixed_mask=fixed_mask_from_spec(spec, n),
        case_id=cid, worker=spec.get("worker", "core"),
        parent_id=spec.get("parent_id"), note=spec.get("note", ""),
        tags=spec.get("tags"), defer_record=needs_prep,
        seed=int(spec.get("seed", 7)),
    )

    # -- preparation: all of it happens BEFORE the t=0 sample is taken --------
    if prep.get("scale_v") is not None:
        s.v = s.v * float(prep["scale_v"])
    if prep.get("reset_u_to") is not None:
        s.u = np.full_like(s.u, float(prep["reset_u_to"]))
    # A "fresh medium" arm means u=1 AND v=0.  Setting only u leaves the parent
    # structure's v in place, and a seed stacked on it can explode.
    if prep.get("reset_v_to") is not None:
        s.v = np.full_like(s.v, float(prep["reset_v_to"]))
    if prep.get("shift_u") is not None:
        sh = prep["shift_u"]
        s.u = np.roll(np.roll(s.u, int(sh.get("dy", 0)), axis=0),
                      int(sh.get("dx", 0)), axis=1)
    if prep.get("shift_v") is not None:
        sh = prep["shift_v"]
        s.v = np.roll(np.roll(s.v, int(sh.get("dy", 0)), axis=0),
                      int(sh.get("dx", 0)), axis=1)
    if float(s.u.min()) < 0 or float(s.v.min()) < 0:
        raise ValueError(f"{cid}: preparation produced a negative concentration "
                         f"(umin={float(s.u.min()):.3e}, vmin={float(s.v.min()):.3e}); "
                         f"clipping is not allowed, fix the spec")
    if prep.get("wait"):
        s.step(int(float(prep["wait"]) / dt))
    if needs_prep:
        s.record_now()

    # -- run ------------------------------------------------------------------
    T = float(spec.get("observe", spec.get("T", 8000)))
    f_switch = spec.get("f_switch")
    if f_switch:
        plan = sorted((float(t), float(fv)) for t, fv in f_switch)
        prev_t = float(s.t)
        for t_apply, f_val in plan:
            if t_apply > prev_t:
                s.step(int((t_apply - prev_t) / dt))
                prev_t = t_apply
            s.f = f_val
        remaining = T - prev_t
        if remaining > 0:
            s.step(int(remaining / dt))
    else:
        s.step(int(T / dt))

    # -- record ---------------------------------------------------------------
    planned = T
    ok, why = s.usable(planned)
    path = s.save(results_dir)
    rec = s.to_record(npz_path=path)
    if not ok and not rec["anomalies"]:
        # Ended short of the planned time without a health failure: still an
        # anomaly, because a short trajectory silently read as a result is the
        # failure mode this check exists to prevent.
        rec["anomalies"] = [why]
        rec["status"] = "failed"
    ledger.append_case(rec, results_dir=results_dir)
    return rec


# --------------------------------------------------------------------------- batch
def load_spec(path: Path | str) -> list[dict]:
    raw = json.loads(Path(path).read_text())
    cases = raw["cases"] if isinstance(raw, dict) else raw
    if not isinstance(cases, list):
        raise ValueError("spec must be a JSON list or {'cases': [...]}")
    return cases


def load_config(path: Path | str) -> tuple[dict | None, list[dict]]:
    """Return ``(meta, cases)``.  ``meta`` is the whole object when the file
    declares an ``experiment_protocol``, else ``None``.

    A registered protocol has to be recognised HERE, before any case is turned
    into a run: the T001 cases deliberately carry no ``n``, so an old-style path
    would fail loudly rather than run a rectangular domain as if it were square.
    """
    raw = json.loads(Path(path).read_text())
    cases = raw["cases"] if isinstance(raw, dict) else raw
    if not isinstance(cases, list):
        raise ValueError("spec must be a JSON list or {'cases': [...]}")
    meta = raw if isinstance(raw, dict) and raw.get("experiment_protocol") else None
    return meta, cases


def run_protocol(meta: dict, args, results_dir: Path) -> int:
    """Execute a registered protocol through its own gating.

    Whole-package runs and STAGE runs take different cost decisions:

    * a whole-package configuration (``configs/T001.json``) is still blocked by the
      64.5-minute projection -- it is not authorized as a single unit;
    * a STAGE configuration (``configs/T001_S1.json``) selects a subset of the
      registered ids, must reproduce their frozen definitions exactly, and is
      compared against the REMAINING cumulative machine-time balance.  Ids outside
      the stage stay visible as ``NOT_RUN_STAGE``.

    Either way the order is: config/task verification, source verification, cost
    decision, per-case dependency gates, and only then a ledger reservation and
    the trajectories.
    """
    from experiment import t001

    stage = None
    if meta.get("stage"):
        stage = t001.load_stage(args.spec)
        cfg = stage["base"]
        stage_cases = stage["cases"]
        stage_ids = [c["case_id"] for c in stage_cases]
    else:
        cfg = t001.load_config(args.spec)
        stage_cases = cfg["cases"]
        stage_ids = None
    t001.check_sources(cfg)

    if args.dry:
        print(json.dumps({"protocol": t001.PROTOCOL, "stage": meta.get("stage"),
                          "cases": len(stage_cases), "dry": True,
                          "stage_ids": stage_ids,
                          "inputs": sorted(t001._frozen_inputs()["inputs"])},
                         indent=2))
        return 0

    if stage is None:
        cost = t001.cost_verdict(cfg)
        state = (t001.NOT_RUN_ENGINEERING if cost["verdict"] == "NOT_RUN"
                 else t001.NOT_RUN_COST)
        for c in cfg["cases"]:
            t001.record_not_run(c["case_id"], state, cost["reason"])
        t001.status(cfg)
        print(json.dumps({"protocol": t001.PROTOCOL, "ran": 0, "status": state,
                          "reason": cost["reason"]}, indent=2))
        return 0

    # --- stage bookkeeping: every registered id stays visible ----------------
    for c in cfg["cases"]:
        if c["case_id"] not in stage_ids and not ledger.already_done(c["case_id"]):
            t001.record_not_run(
                c["case_id"], t001.NOT_RUN_STAGE,
                f"registered but outside the authorized stage {stage['stage']} "
                f"({sorted(stage_ids)}); the following stage needs its own "
                f"authorization")
    cost = t001.stage_cost(cfg, stage_ids, stage.get("allowance"))
    # pre-run guard over EVERY account: nothing starts unless each one has headroom
    guard = t001.preflight_budget(cfg, stage, cost)
    t001.stage_artifacts(stage, cfg, tag="before", cost=cost, guard=guard)
    t001._write_json(t001.STAGE_ROOT / "preflight.json", guard)
    if not guard["ok"]:
        bad = {k: v for k, v in guard["checks"].items() if not v["ok"]}
        for c in stage_cases:
            t001.record_not_run(c["case_id"], t001.NOT_RUN_BUDGET,
                                f"pre-run budget guard failed: {sorted(bad)}")
        t001.status(cfg)
        print(json.dumps({"protocol": t001.PROTOCOL, "stage": stage["stage"], "ran": 0,
                          "status": t001.NOT_RUN_BUDGET, "guard_failed": sorted(bad)},
                         indent=2))
        return 0
    if cost["verdict"] != "PASS":
        state = (t001.NOT_RUN_ENGINEERING if cost["verdict"] == "NOT_RUN"
                 else t001.NOT_RUN_COST)
        for c in stage_cases:
            t001.record_not_run(c["case_id"], state, cost["reason"])
        t001.status(cfg)
        print(json.dumps({"protocol": t001.PROTOCOL, "stage": stage["stage"], "ran": 0,
                          "status": state, "reason": cost["reason"]}, indent=2))
        return 0

    runnable = [c for c in stage_cases if not ledger.already_done(c["case_id"])]
    blocked, todo = [], []
    for c in runnable:
        why = t001.gate_reason(c)
        if why:
            t001.record_not_run(c["case_id"], t001.NOT_RUN_GATE, why)
            blocked.append({"case_id": c["case_id"], "status": t001.NOT_RUN_GATE,
                            "reason": why})
        else:
            todo.append(c)
    for b in blocked:
        print(json.dumps(b, ensure_ascii=False))
    if not todo:
        t001.status(cfg)
        print(json.dumps({"protocol": t001.PROTOCOL, "stage": stage["stage"],
                          "runnable": 0, "skipped": len(stage_cases) - len(runnable),
                          "gated": len(blocked)}, indent=2))
        return 0

    budget = t001.Budget(cfg, allowance=stage.get("allowance"))
    reserved = None
    if not args.allow_over_cap:
        reserved = ledger.reserve(len(todo), purpose=args.purpose,
                                  batch_id=args.batch_id)
    done = actual = 0
    try:
        for c in todo:
            over, why_over = t001.budget_stop(budget)
            if over:
                # the cap is cumulative: the remaining cases are not started, and
                # are recorded as such rather than silently dropped
                for c2 in todo[todo.index(c):]:
                    t001.record_not_run(c2["case_id"], t001.NOT_RUN_BUDGET, why_over)
                print(json.dumps({"stage": stage["stage"], "stopped": t001.NOT_RUN_BUDGET,
                                  "reason": why_over}, ensure_ascii=False))
                break
            rec = t001.run_case(c, cfg, results_dir, budget=budget, stage=stage)
            actual += 1
            done += 1
            budget.charge_main(rec["t001"]["cell_steps"])
            print(json.dumps({"case_id": rec["case_id"], "status": rec["status"],
                              "t001_status": rec["t001"]["execution_status"],
                              "verdict": rec["t001"]["mechanism_verdict"],
                              "t_final": rec.get("t_final"),
                              "anomalies": rec.get("anomalies")}, default=str))
        t001.status(cfg)
    finally:
        if reserved is not None:
            ledger.settle(reserved, actual=actual)
    t001.stage_artifacts(stage, cfg, tag="after")
    print(json.dumps({"protocol": t001.PROTOCOL, "stage": stage["stage"],
                      "requested": len(cfg["cases"]), "stage_cases": len(stage_cases),
                      "ran": done, "gated": len(blocked),
                      "results_dir": str(results_dir)}, indent=2))
    return 0
def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="declarative Gray-Scott batch runner")
    ap.add_argument("spec", help="JSON list of cases, or {'cases': [...]}")
    ap.add_argument("--dry", action="store_true",
                    help="resolve each case but do not integrate or write")
    ap.add_argument("--probe-steps", type=int, default=0,
                    help="T009: run the cost calibration with this many equation steps "
                         "(cumulative hard cap 128 across all calls)")
    ap.add_argument("--cost-only", action="store_true",
                    help="T004: run the input preflight and the cost gate, then stop")
    ap.add_argument("--probe", action="store_true",
                    help="analysis-only configs: run the 3-snapshot cost probe and stop")
    ap.add_argument("--recheck-alignment", action="store_true",
                    help="analysis-only configs: re-derive only the B candidate window and "
                         "its departure under the corrected alignment (budget-frugal)")
    ap.add_argument("--max-runs", type=int, default=None,
                    help="hard cap on cases run by THIS invocation")
    ap.add_argument("--allow-over-cap", action="store_true",
                    help="run even when the shared ledger quota is exhausted")
    ap.add_argument("--batch-id", default=None,
                    help="label for the atomic quota reservation")
    ap.add_argument("--purpose", default="", help="human note on the reservation")
    ap.add_argument("--ledger-limit", type=int, default=None,
                    help="override the ledger's trajectory limit")
    ap.add_argument("--ledger", default=None, help="ledger JSON path override")
    ap.add_argument("--results-dir", default=None, help="results directory override")
    ap.add_argument("--cases", default=None, help="cases.jsonl path override")
    args = ap.parse_args(argv)

    results_dir = Path(args.results_dir) if args.results_dir else ledger.RESULTS
    if args.results_dir or args.ledger or args.cases:
        ledger.set_results_dir(results_dir, ledger_path=args.ledger,
                               cases_path=args.cases)
    if args.ledger_limit is not None:
        ledger.set_limit(args.ledger_limit)

    meta, cases = load_config(args.spec)
    if meta is not None:
        if meta["experiment_protocol"] == "T001_v1":
            return run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R028_AFTERSTATE_CONTINUATION_v1":
            # T060: continue both T058 terminals, WAIT first, no injection.
            from experiment import t060
            return t060.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R028_B_CONTROL_v1":
            # T059: B after-state idle then first D injection; A not re-run.
            from experiment import t059
            return t059.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R028_REPEATED_QUERY_v1":
            # T058: A after-state idle then second D injection; B not run.
            from experiment import t058
            return t058.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R028_SUCCESSOR_QUERY_S1_v1":
            # T054 = T053 phase 2: S1 idle then query; S0 not re-run.
            from experiment import t054
            return t054.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R028_SUCCESSOR_QUERY_v1":
            # T053 phase 1: S0 idle then query; S1 static-only.
            from experiment import t053
            return t053.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_QC_JOINT_v1":
            # T052: the single Q+C joint-field branch (dual identity).
            from experiment import t052
            return t052.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_CARRIER_STAGE1_v1":
            # T050: free carrier first, WAIT+C behind the stage gate.
            from experiment import t050
            return t050.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_INPUT_SHIFT7_v1":
            # T047: fixed +7-column input shift, three branches
            # (no-downstream / S6 / S8) to t=120000.
            from experiment import t047
            return t047.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_DOWNSTREAM_S6_STATE_v1":
            # T046: fixed same-position downstream S6 state vs T043's S8 state.
            from experiment import t046
            return t046.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_CONTROL_CONTINUATION_v1":
            # T044: no-downstream control continued from the actual T042 72000 fields.
            from experiment import t044
            return t044.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_JOINT_FIELD_v1":
            # T043: fixed common field (S6 base + shifted downstream S8) to 120000.
            from experiment import t043
            return t043.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_VERTICAL_EXTENSION_v1":
            # T042: fixed ny 256->512 extension; S6 passthrough + S8 early split.
            from experiment import t042
            return t042.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_RELAX_RESTART_v1":
            # T039: external restart from the actual T038 no-Q t=100 fields + same Q.
            from experiment import t039
            return t039.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_SINGLE_COMPONENT_v1":
            # T038: the two single-component counterfactuals M_u/M_v +/- the same Q.
            from experiment import t038
            return t038.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_SPATIAL_PARTITION_v1":
            # T037: fixed field-difference partitions M_R/M_L ± the same Q.
            from experiment import t037
            return t037.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_ALPHA0375_v1":
            # T036: the single pre-fixed weight alpha=0.375 ± the same Q.
            from experiment import t036
            return t036.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_ALPHA_WEIGHTS_v1":
            # T035: two pre-fixed S6/S8 weights ± the same Q.
            from experiment import t035
            return t035.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_MIDPOINT_v1":
            # T034: single S6/S8 midpoint counterfactual ± the same Q.
            from experiment import t034
            return t034.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_S8_Q_DT0125_v1":
            # T032: single-branch dt=0.125 screen on T029 S8_Q.
            from experiment import t032
            return t032.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_Q_XP7_v1":
            # T031: +7-column free and S8 queries.
            from experiment import t031
            return t031.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R027_S8_Q_DIAG_v1":
            # T029: eight-core state ± moving Q.
            from experiment import t029
            return t029.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R026_SECOND_CELL_v1":
            # T028: second conditional cell + full B/P history.
            from experiment import t028
            return t028.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R026_RCV_SCREEN_v1":
            # T027: fixed receiver × moving query, controls first.
            from experiment import t027
            return t027.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R023_PZERO_INPUTS_v1":
            # T024: the two p=0 branches (B_R, AB_R), B_R first.
            from experiment import t024
            return t024.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R022_BP_H2_v1":
            # T023: the fine-grid BP branch, stage A (recovery validation first).
            from experiment import t023
            return t023.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R020_BP_DT0125_v1":
            # T022: the single BP branch with dt halved to 0.125.
            from experiment import t022
            return t022.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R019_LIVE_HANDOFF_ABP_v1":
            # T021 stage C: the blocked upstream control only; WAIT/BP are the
            # stored pairing references and are never re-run.
            from experiment import t021_abp
            return t021_abp.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R019_LIVE_HANDOFF_BP_v1":
            # T021 stage B: the real BP pass history only; WAIT is the stored
            # pairing reference and ABP_R stays NOT_RUN_STAGE_GATE.
            from experiment import t021_bp
            return t021_bp.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R019_LIVE_HANDOFF_v1":
            # T021 stage A: the joint-field empty-wait branch only.  The two
            # pass/block branches are registered but stay NOT_RUN_STAGE_GATE.
            from experiment import t021
            return t021.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R015_DOWN_QUERY_S6_v1":
            # T017 stage S6: the two six-core source trajectories.
            from experiment import t017_s6
            return t017_s6.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R015_DOWN_QUERY_v1":
            # T017 stage A only: the single free downward query.
            from experiment import t017
            return t017.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R013_P_YSHIFT1_v1":
            # T015: the single +y-row late-P trajectory, thin over the t014 loop.
            from experiment import t015
            return t015.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R012_Q4_SEQUENCE_v1":
            # T014: three Q4 sequence branches with the paired preparation stage.
            from experiment import t014
            return t014.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R011_Q6_RESPONSE_v1":
            # T013: the two mature-six-core response diagnostics.  It has its own
            # compact W code and V mechanism labels; the T010 total verdicts are not
            # reused.  Every actual launch archives the executed sources itself.
            from experiment import t013
            return t013.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R009_DT_v1":
            # T011: dt=0.25 sensitivity runs, thin-adapted over the t010 loop.
            from experiment import t011
            return t011.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R008_B0_v1":
            # T010: the thin R008-B0 entry.  It uses the Agent-1 science module and the
            # original frozen baseline; the retired T009 path is NOT called.
            from experiment import t010
            return t010.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R007B0_v1":
            # T009: the R007-B0 six-case coarse stage.  It reads its own immutable
            # authorization baseline and refuses unexplained ledger drift.
            from experiment import t009
            return t009.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R003A_v1":
            # T004: the six-case bypass-probe stage.  It has its own authorization
            # table, its own grids and its own criteria; its config is refused unless
            # it matches the authorized limits and case list exactly.
            from experiment import t004
            return t004.run_protocol(meta, args, results_dir)
        if meta["experiment_protocol"] == "R002_analysis_v1":
            # READ-ONLY analysis of already-stored trajectories (T003): it never enters
            # run_one, never reserves a trajectory and never advances a PDE.  The
            # module's own config validation refuses a non-analysis or unknown config.
            from experiment import t003
            return t003.run_analysis(meta, args, results_dir)
        raise SystemExit(f"unknown experiment_protocol {meta['experiment_protocol']!r}: "
                         f"refusing to guess how to run it")
    if args.max_runs is not None:
        cases = cases[:args.max_runs]
    runnable = [c for c in cases if not ledger.already_done(c["case_id"])]
    if not runnable:
        print(json.dumps({"cases": len(cases), "runnable": 0,
                          "skipped": len(cases)}, indent=2))
        return 0
    if args.dry:
        for c in runnable:
            print(json.dumps(run_one(c, results_dir, dry=True), default=str))
        return 0

    reservation = None
    if not args.allow_over_cap:
        # Reserve BEFORE starting: two concurrent batches must not each respect
        # their own cap and still overrun the shared pool.
        reservation = ledger.reserve(len(runnable), purpose=args.purpose,
                                     batch_id=args.batch_id)
    done = actual = 0
    try:
        for c in runnable:
            rec = run_one(c, results_dir)
            actual += 1
            if rec.get("skipped"):
                continue
            done += 1
            fm = rec.get("final_metrics", {})
            print(json.dumps({"case_id": rec["case_id"], "status": rec["status"],
                              "Mv": fm.get("Mv"), "vmax": fm.get("vmax"),
                              "t_final": rec.get("t_final"),
                              "anomalies": rec.get("anomalies")}, default=str))
    finally:
        if reservation is not None:
            ledger.settle(reservation, actual=actual)
    print(json.dumps({"requested": len(cases), "ran": done,
                      "attempted": actual, "results_dir": str(results_dir)},
                     indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
