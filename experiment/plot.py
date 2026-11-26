"""The one place data figures are drawn -- Pillow only, no plotting library.

Why a single module
-------------------
When every work package draws its own figure, the same field ends up shown under
several colour scales, and two panels of one comparison stop being comparable
without anyone noticing.  Every primitive here therefore takes ``vmax`` and
defaults to a module-level frozen scale (:data:`FROZEN_VMAX`) instead of
auto-scaling to the data.  Nothing in this module silently rescales a panel.

Primitives
----------
``ramp(field, vmax)``            scalar field -> float RGB in [0, 1]
``field_png(field, path, ...)``  one field, one PNG
``contact_sheet(fields, labels, path, ...)``  a grid, one frozen scale
``curve(x, y, path, ...)``       line plot from plain sequences
``series_from_frames(npz, ...)`` ``frames_v``/``frames_u``/``frames_t`` -> series

The generic ``overlay`` argument draws the zero-crossing contour of an arbitrary
companion array, so a driver field can be shown without this module knowing what
a "resource" is.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np
from PIL import Image, ImageDraw, ImageFont

REPO = Path(__file__).resolve().parent.parent

# Frozen colour scale: figures in a set are only comparable if they share it.
FROZEN_VMAX = 0.5
BACKGROUND = "#0e131b"
LABEL_COLOUR = "#c8d4e0"
AXIS_COLOUR = "#9fb0c0"
TICK_COLOUR = "#7f8fa3"
FRAME_COLOUR = "#26303d"
OVERLAY_RGB = (0.1, 1.0, 0.1)
SERIES_RGB = ((255, 120, 120), (120, 220, 160), (140, 170, 255),
              (240, 200, 90), (220, 140, 240), (150, 150, 150))


# --------------------------------------------------------------------- palette
def ramp(field: np.ndarray, vmax: float = FROZEN_VMAX) -> np.ndarray:
    """Map a scalar field to float RGB via the fixed black-blue-green ramp.

    ``vmax`` is required to be positive rather than inferred: a zero span would
    otherwise divide by zero into a blank figure that still looks deliberate.
    """
    if vmax <= 0:
        raise ValueError(f"vmax must be > 0, got {vmax!r}")
    a = np.asarray(field, dtype=np.float64)
    g = np.clip(a / float(vmax), 0.0, 1.0)
    return np.stack([np.clip(g * 3.0 - 1.2, 0.0, 1.0),
                     np.clip(g * 2.0 - 0.3, 0.0, 1.0),
                     g], axis=-1)


def overlay_mask(overlay: np.ndarray) -> np.ndarray:
    """Boolean mask of cells where ``overlay - mean(overlay)`` changes sign.

    This is the generic form of "draw the driver": the contour of any companion
    array is meaningful, while the identity of the array is not this module's
    business.  A uniform overlay yields an empty mask.
    """
    a = np.asarray(overlay, dtype=np.float64)
    if a.ndim != 2 or min(a.shape) < 2:
        return np.zeros(a.shape, bool)
    r = a - a.mean()
    s = np.sign(r)
    edge = np.zeros(a.shape, bool)
    edge[1:-1, 1:-1] = (
        (np.abs(np.diff(s, axis=0))[:-1, 1:-1] > 0)
        | (np.abs(np.diff(s, axis=1))[1:-1, :-1] > 0))
    return edge


def apply_overlay(rgb: np.ndarray, overlay: np.ndarray | None) -> np.ndarray:
    """Paint the contour of ``overlay`` onto an RGB image (a copy is returned)."""
    out = np.array(rgb, dtype=np.float64, copy=True)
    if overlay is None:
        return out
    a = np.asarray(overlay)
    if a.shape != out.shape[:2]:
        raise ValueError(f"overlay shape {a.shape} != field shape {out.shape[:2]}")
    out[overlay_mask(a)] = OVERLAY_RGB
    return out


def font(size: int = 13) -> ImageFont.ImageFont:
    """A TrueType font when the platform has one, else Pillow's bitmap default."""
    for candidate in ("/System/Library/Fonts/Supplemental/Arial.ttf",
                      "/System/Library/Fonts/Helvetica.ttc",
                      "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"):
        try:
            return ImageFont.truetype(candidate, size)
        except OSError:
            continue
    return ImageFont.load_default()


def _to_image(rgb: np.ndarray, size: int) -> Image.Image:
    return Image.fromarray((np.clip(rgb, 0.0, 1.0) * 255).astype(np.uint8)).resize(
        (size, size), Image.Resampling.NEAREST)


def _save(im: Image.Image, path: Path | str) -> Path:
    out = Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    im.save(out)
    return out


# ------------------------------------------------------------------ primitives
def field_png(field: np.ndarray, path: Path | str, size: int = 260, title: str = "",
              vmax: float = FROZEN_VMAX, overlay: np.ndarray | None = None) -> Path:
    """One scalar field as a PNG, with an optional companion contour overlay."""
    rgb = apply_overlay(ramp(field, vmax), overlay)
    im = _to_image(rgb, size)
    if title:
        sheet = Image.new("RGB", (size, size + 22), BACKGROUND)
        sheet.paste(im, (0, 0))
        ImageDraw.Draw(sheet).text((2, size + 3), title[:48], font=font(12),
                                   fill=LABEL_COLOUR)
        im = sheet
    return _save(im, path)


def contact_sheet(fields: Sequence[np.ndarray], labels: Sequence[str],
                  path: Path | str, cols: int = 4, size: int = 200,
                  title: str = "", vmax: float = FROZEN_VMAX,
                  overlays: Sequence[np.ndarray | None] | None = None) -> Path:
    """A grid of fields under ONE colour scale (``vmax``, never per panel).

    ``labels`` shorter than ``fields`` is padded rather than raising: a missing
    caption is a cosmetic problem, a refused figure is a lost comparison.
    """
    fields = list(fields)
    if not fields:
        raise ValueError("contact_sheet needs at least one field")
    if cols < 1:
        raise ValueError(f"cols must be >= 1, got {cols!r}")
    labels = list(labels) + [""] * max(0, len(fields) - len(labels))
    overlays = list(overlays) if overlays is not None else [None] * len(fields)

    rows = (len(fields) + cols - 1) // cols
    sheet = Image.new("RGB", (cols * (size + 8) + 8, rows * (size + 30) + 46),
                      BACKGROUND)
    draw = ImageDraw.Draw(sheet)
    if title:
        draw.text((10, 12), title, font=font(16), fill="white")
    for i, field in enumerate(fields):
        rgb = apply_overlay(ramp(field, vmax), overlays[i])
        img = _to_image(rgb, size)
        x = 8 + (i % cols) * (size + 8)
        y = 42 + (i // cols) * (size + 30)
        sheet.paste(img, (x, y))
        draw.text((x, y + size + 3), str(labels[i])[:30], font=font(11),
                  fill=LABEL_COLOUR)
    return _save(sheet, path)


def _rotated_label(im, text: str, centre: tuple[int, int]) -> None:
    """Draw ``text`` rotated 90 degrees, centred vertically at ``centre``."""
    if not text:
        return
    f = font(12)
    probe = Image.new("RGBA", (1, 1))
    tw = probe.size and f.getbbox(text)
    w, h = tw[2] - tw[0] + 4, tw[3] - tw[1] + 4
    tmp = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    ImageDraw.Draw(tmp).text((-tw[0] + 2, -tw[1] + 2), text, font=f, fill=AXIS_COLOUR)
    tmp = tmp.rotate(90, expand=True)
    im.paste(tmp, (centre[0], centre[1] - tmp.height // 2), tmp)


def curve(x: Sequence[float], y: Sequence[float], path: Path | str,
          xlabel: str = "x", ylabel: str = "y", title: str = "", label: str = "",
          extra_series: Sequence[tuple[str, Sequence[float], Sequence[float]]] | None = None,
          width: int = 900, height: int = 420) -> Path:
    """A line plot.

    ``extra_series`` adds ``(label, xs, ys)`` triples so several runs can share
    one figure and one pair of axes.  Non-finite samples split the line instead
    of being drawn at a fake position, which is what a gap in a track means.
    """
    series: list[tuple[str, list[float], list[float]]] = [
        (label, list(map(float, x)), list(map(float, y)))]
    for lab, xs, ys in (extra_series or ()):
        series.append((str(lab), list(map(float, xs)), list(map(float, ys))))

    im = Image.new("RGB", (width, height), BACKGROUND)
    draw = ImageDraw.Draw(im)
    draw.text((10, 8), title, font=font(15), fill="white")
    left, right, top, bottom = 70, width - 150, 40, height - 40
    draw.rectangle([left, top, right, bottom], outline=FRAME_COLOUR)

    finite = [(sx, sy) for _, xs, ys in series
              for sx, sy in zip(xs, ys) if math.isfinite(sx) and math.isfinite(sy)]
    if not finite:
        draw.text((left + 8, top + 8), "no finite samples", font=font(13),
                  fill=TICK_COLOUR)
        return _save(im, path)

    xs_all = [p[0] for p in finite]
    ys_all = [p[1] for p in finite]
    x0, x1 = min(xs_all), max(xs_all)
    y0, y1 = min(ys_all), max(ys_all)
    if x1 - x0 < 1e-12:
        x0, x1 = x0 - 0.5, x1 + 0.5
    if y1 - y0 < 1e-12:
        y0, y1 = y0 - 0.5, y1 + 0.5

    for i, (lab, xs, ys) in enumerate(series):
        colour = SERIES_RGB[i % len(SERIES_RGB)]
        segment: list[tuple[float, float]] = []
        for sx, sy in zip(xs, ys):
            if not (math.isfinite(sx) and math.isfinite(sy)):
                if len(segment) > 1:
                    draw.line(segment, fill=colour, width=2)
                segment = []
                continue
            segment.append((left + (sx - x0) / (x1 - x0) * (right - left),
                            bottom - (sy - y0) / (y1 - y0) * (bottom - top)))
        if len(segment) > 1:
            draw.line(segment, fill=colour, width=2)
        if lab:
            draw.text((right + 6, top + 14 * i), lab[:20], font=font(11),
                      fill=colour)

    draw.text((left, bottom + 8), xlabel[:60], font=font(12), fill=AXIS_COLOUR)
    # The y label is rotated so it cannot collide with the tick values or the
    # title, which is what a horizontal label in a 70 px left margin always did.
    _rotated_label(im, ylabel[:28], (4, (top + bottom) // 2))
    draw.text((left + 4, bottom - 16), f"{x0:.3g} .. {x1:.3g}", font=font(11),
              fill=TICK_COLOUR)
    draw.text((left + 4, top + 4), f"{y1:.3g}", font=font(11), fill=TICK_COLOUR)
    draw.text((left + 4, bottom - 32), f"{y0:.3g}", font=font(11),
              fill=TICK_COLOUR)
    return _save(im, path)


# -------------------------------------------------------------------- ledger io
def results_dir() -> Path:
    """The results root without a hardcoded path.

    ``$GS_RESULTS_DIR`` wins (tests), then the ledger's own ``RESULTS`` if
    :mod:`experiment.ledger` can be imported, then ``REPO/results``.  Deliberately
    a few lines duplicated from :mod:`experiment.analyze`: keeping this module
    free of the ``core`` import is what lets figures be drawn on a machine that
    only has numpy and Pillow.
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


def _open_npz(obj: Any) -> Any:
    if isinstance(obj, (str, Path)):
        return np.load(Path(obj))
    if hasattr(obj, "__getitem__") and hasattr(obj, "__contains__"):
        return obj
    raise TypeError(f"cannot read frames from {type(obj).__name__}")


def series_from_frames(npz: Any, field: str = "v",
                       h: float | None = None) -> dict | None:
    """Per-frame series pulled from a stored run.

    Reads ``frames_v`` (or ``frames_u``) and ``frames_t`` and returns
    ``{t, mass, Mv, cy, cx, Rg, frames, field}``; ``None`` when the run stored no
    frames.  ``mass`` is the area-weighted ``h**2 * sum(field)`` so it matches the
    ``Mv`` that :func:`core.gs.metrics` reports (``Mv`` is kept as an alias for
    the ``v`` series).

    ``cy``/``cx``/``Rg`` are ``nan`` for a frame with no support, so callers can
    see the gap rather than a fabricated centroid.
    """
    z = _open_npz(npz)
    key = f"frames_{field}"
    if key not in z:
        return None
    frames = np.asarray(z[key], dtype=np.float64)
    n_frames = frames.shape[0]
    t = (np.asarray(z["frames_t"], dtype=np.float64)
         if "frames_t" in z else np.arange(n_frames, dtype=np.float64))
    if h is not None:
        grid_h = float(h)
    elif "h" in z:
        grid_h = float(np.asarray(z["h"]).reshape(-1)[0])
    else:
        grid_h = 1.0

    X, Y = np.indices(frames.shape[1:])
    mass = np.empty(n_frames, dtype=np.float64)
    cy = np.empty(n_frames, dtype=np.float64)
    cx = np.empty(n_frames, dtype=np.float64)
    rg = np.empty(n_frames, dtype=np.float64)
    for i, a in enumerate(frames):
        total = float(a.sum())
        mass[i] = grid_h ** 2 * total
        if total <= 0:
            cy[i] = cx[i] = rg[i] = float("nan")
            continue
        ybar = float((a * X).sum() / total)
        xbar = float((a * Y).sum() / total)
        cy[i], cx[i] = ybar, xbar
        rg[i] = grid_h * float(np.sqrt(
            (a * ((X - ybar) ** 2 + (Y - xbar) ** 2)).sum() / total))

    out = {"t": t, "mass": mass, "cy": cy, "cx": cx, "Rg": rg,
           "frames": frames, "field": field}
    if field == "v":
        out["Mv"] = mass
    return out


def load_cases(root: Path | str | None = None) -> list[dict]:
    """Read ``<root>/cases.jsonl`` (default: :func:`results_dir`); [] if absent."""
    path = (Path(root) if root is not None else results_dir()) / "cases.jsonl"
    if not path.exists():
        return []
    records: list[dict] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            records.append(obj)
    return records


def _resolve_npz(rec: Mapping[str, Any], root: Path) -> Path:
    raw = rec.get("npz_path")
    if raw:
        p = Path(str(raw))
        if p.is_absolute():
            return p
        for cand in (REPO / p, root / p):
            if cand.exists():
                return cand
        return REPO / p
    return root / f"{rec.get('case_id')}.npz"


# ------------------------------------------------------------------------- CLI
def _draw_fields(records: list[dict], root: Path, outdir: Path, max_fields: int,
                 vmax: float) -> list[Path]:
    fields: list[np.ndarray] = []
    overlays: list[np.ndarray | None] = []
    labels: list[str] = []
    for rec in records:
        if len(fields) >= max_fields:
            break
        path = _resolve_npz(rec, root)
        if not path.exists():
            continue
        with np.load(path) as z:
            if "v" not in z:
                continue
            v = np.asarray(z["v"], dtype=np.float64)
            # An overlay is only attached when the companion array is actually
            # non-uniform; a flat one would only add noise.
            ov = None
            if "ures" in z:
                ures = np.asarray(z["ures"], dtype=np.float64)
                if ures.size and float(ures.max() - ures.min()) > 1e-9:
                    ov = ures
        fm = rec.get("final_metrics") or {}
        mv = fm.get("Mv")
        mv_text = f"{float(mv):.3g}" if isinstance(mv, (int, float)) else "n/a"
        labels.append(f"{str(rec.get('case_id'))[:22]} "
                      f"Mv={mv_text} t={rec.get('t_final')}")
        fields.append(v)
        overlays.append(ov)
    if not fields:
        return []
    # Only advertise the overlay when at least one panel actually has one;
    # a legend for something that is not drawn is worse than no legend.
    has_overlay = any(o is not None for o in overlays)
    title = f"final v fields | frozen colour scale 0-{vmax:g}"
    if has_overlay:
        title += " | green = overlay zero crossing"
    return [contact_sheet(fields, labels, outdir / "contact.png",
                          vmax=vmax, overlays=overlays, title=title)]


def _draw_series(records: list[dict], root: Path, outdir: Path,
                 max_fields: int) -> list[Path]:
    made: list[Path] = []
    extra: list[tuple[str, Sequence[float], Sequence[float]]] = []
    first: tuple[Sequence[float], Sequence[float]] | None = None
    for rec in records:
        if len(extra) + (1 if first else 0) >= max_fields:
            break
        path = _resolve_npz(rec, root)
        if not path.exists():
            continue
        with np.load(path) as z:
            data = series_from_frames(z, field="v")
        if data is None:
            continue
        label = str(rec.get("case_id"))[:18]
        if first is None:
            first = (data["t"], data["Mv"])
            first_label = label
            continue
        extra.append((label, data["t"], data["Mv"]))
    if first is None:
        return made
    made.append(curve(first[0], first[1], outdir / "mv_vs_t.png",
                      xlabel="model time", ylabel="Mv (area-weighted)",
                      title="Mv(t) from stored frames",
                      label=first_label, extra_series=extra))
    return made


def main(argv: list[str] | None = None) -> int:
    """CLI: draw the standard figures from the ledger's stored arrays."""
    ap = argparse.ArgumentParser(
        prog="python -m experiment.plot",
        description="Write field contact sheets and frame-series curves (PIL only).")
    ap.add_argument("--filter", default=None, metavar="SUBSTR",
                    help="only records whose case_id contains SUBSTR")
    ap.add_argument("--max-fields", type=int, default=12, metavar="N",
                    help="cap on panels per figure (default: 12)")
    ap.add_argument("--series", action="store_true",
                    help="also plot Mv(t) from the stored frame stacks")
    ap.add_argument("--outdir", default=None, metavar="PATH",
                    help="figure destination (default: <results>/figs)")
    ap.add_argument("--vmax", type=float, default=FROZEN_VMAX, metavar="V",
                    help=f"frozen colour-scale maximum (default: {FROZEN_VMAX})")
    args = ap.parse_args(argv)

    root = results_dir()
    outdir = Path(args.outdir) if args.outdir else root / "figs"
    records = load_cases(root)
    if args.filter:
        records = [r for r in records
                   if args.filter in str(r.get("case_id") or "")]

    made = _draw_fields(records, root, outdir, max(0, args.max_fields), args.vmax)
    if args.series:
        made += _draw_series(records, root, outdir, max(1, args.max_fields))

    print(f"plot: {len(records)} records from {root}")
    if not made:
        print("  nothing drawn (no records with stored arrays"
              f"{'/frames' if args.series else ''})")
        return 0
    print(f"  frozen colour scale 0-{args.vmax:g}")
    for p in made:
        print(f"  -> {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
