"""validate.py -- the single enforcement point for the record contract.

Every record written by the harness is checked here before it is stored.  The
invariant matters because a rejected record at write time costs one edit, while
an index that accumulated several mutually incompatible shapes of the same
concept is only visible long after the runs are gone -- by then the numeric
results cannot be re-derived, only excluded.

The engine is declarative: schema.json owns the field list, this module owns the
rules.  Adding a field is a schema edit, never a code edit.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parent.parent
SCHEMA_PATH = Path(__file__).resolve().parent / "schema.json"
DEFAULT_CASES = REPO / "results" / "cases.jsonl"

SCHEMA: dict[str, Any] = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))

# "float" admits int so that a whole-valued JSON number (n=1.0) is not rejected
# on a technicality; bool is checked separately so it cannot masquerade as int.
PY_TO_TYPE: dict[str, Any] = {"str": str, "int": int, "float": (int, float),
                              "bool": bool, "dict": dict, "list": list}

# Fields that describe the geometry of a structure and are therefore meaningless
# when the run reports none.  Values (Mv, vmax) are never in this set: they are
# always required, even for an extinct run.  "components" is the decomposition of
# the structure, so it shares the geometry rule.
DEFAULT_SHAPE_FIELDS = ("Rg", "components", "centroid", "cx", "cy")


def validate_record(rec: dict) -> list[str]:
    """Return the contract violations in ``rec``; an empty list means valid."""
    errs: list[str] = []
    fm = rec.get("final_metrics") or {}

    for k in SCHEMA["required"]:
        if k not in rec:
            errs.append(f"missing required field '{k}'")

    for k, t in SCHEMA["types"].items():
        if k not in rec or rec[k] is None:
            continue
        name = t.replace("|null", "")
        expected = PY_TO_TYPE.get(name)
        if expected is None:
            continue
        value = rec[k]
        if isinstance(value, bool) and name in ("int", "float"):
            errs.append(f"field '{k}' should be {name}, got bool")
        elif not isinstance(value, expected):
            errs.append(f"field '{k}' should be {name}, got {type(value).__name__}")

    for k, allowed in SCHEMA["enums"].items():
        if k in rec and rec[k] is not None and rec[k] not in allowed:
            errs.append(f"field '{k}' = {rec[k]!r} not in {allowed}")

    # ---- final_metrics field rules -------------------------------------
    # Two classes of final metric, with different obligations:
    #   VALUE fields (Mv, vmax): always required, never null, because "how much
    #       material is there" is answerable even when there is no structure.
    #   SHAPE fields (Rg, components, centroid, cx, cy): describe the geometry of
    #       the structure, so a null is honest ONLY when the record also says
    #       there is none.  Requiring a fabricated number here, or rejecting an
    #       honest null, would both corrupt the index, so the rule is stated in
    #       both directions.
    aliases = SCHEMA.get("final_metrics_aliases", {})
    shape_fields = set(SCHEMA.get("final_metrics_shape_fields", DEFAULT_SHAPE_FIELDS))
    no_structure = (fm.get("vmax") in (None, 0)
                    or int(fm.get("active_area_cells") or 0) == 0)

    for req in SCHEMA["final_metrics_required"]:
        alt = [a for a, canon in aliases.items() if canon == req]
        present = req in fm or any(a in fm for a in alt)
        value = next((fm[k] for k in (req, *alt) if fm.get(k) is not None), None)
        if req in shape_fields:
            if value is not None or no_structure:
                continue
            if present:
                errs.append(
                    f"final_metrics '{req}' is null but the run reports a "
                    f"structure (vmax={fm.get('vmax')}, "
                    f"active_area_cells={fm.get('active_area_cells')})")
            else:
                errs.append(f"final_metrics missing '{req}'")
            continue
        if value is None:
            errs.append(f"final_metrics missing '{req}'")

    if rec.get("status") == "failed" and not rec.get("anomalies"):
        errs.append("status=failed but no anomaly recorded (silent failure?)")

    res = rec.get("resource")
    if isinstance(res, dict) and "kind" not in res:
        errs.append("resource dict has no 'kind' (cannot tell what drove the run)")
    return errs


def load_records(path: str | Path | None = None) -> list[dict]:
    """Read a JSONL record index.  A malformed line is an error, not a skip:
    silently dropping a line would hide exactly the corruption this module is
    meant to catch."""
    p = Path(path) if path is not None else DEFAULT_CASES
    if not p.exists():
        return []
    recs = []
    for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            recs.append(json.loads(line))
        except json.JSONDecodeError as exc:
            raise ValueError(f"{p}:{i}: malformed JSON record: {exc}") from exc
    return recs


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Validate a JSONL record index against schema.json.")
    ap.add_argument("--cases", default=str(DEFAULT_CASES),
                    help=f"record index to check (default: {DEFAULT_CASES})")
    ap.add_argument("--max-report", type=int, default=12,
                    help="how many individual bad records to print")
    args = ap.parse_args(argv)

    p = Path(args.cases)
    if not p.exists():
        print(f"no cases file at {p}")
        return 1
    recs = load_records(p)
    bad: list[tuple[str, list[str]]] = []
    for i, r in enumerate(recs):
        errs = validate_record(r)
        if errs:
            bad.append((str(r.get("case_id", f"<line {i + 1}>")), errs))

    print(f"validated {len(recs)} records; {len(bad)} with problems "
          f"({100 * len(bad) / max(len(recs), 1):.1f}%)")
    kinds = Counter(e.split("'")[1] if "'" in e else e[:40]
                    for _, errs in bad for e in errs)
    for k, v in kinds.most_common(10):
        print(f"  {v:5d}  {k}")
    for cid, errs in bad[:args.max_report]:
        print(f"  {cid}: {errs[0]}")
    return 0 if not bad else 2


if __name__ == "__main__":
    sys.exit(main())
