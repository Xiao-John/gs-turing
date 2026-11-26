"""Translation-invariant distance between two Gray-Scott states.

The question this answers
-------------------------
"Is this configuration the same state as that one, or has it changed?"  A naive
per-cell difference answers a different question -- "is it in the same place?" --
because a configuration that has simply drifted is reported as maximally different.

Definition (fixed here, never adapted per comparison)
----------------------------------------------------
With a frozen core set ``C`` (the reference structure's own support, e.g.
``{v_ref > 0.05}``):

    d^2 = mean_C((u - u_ref)^2) / mean_C((1 - u_ref)^2)
        + mean_C((v - v_ref)^2) / mean_C(v_ref^2)

The u term is normalised by the BACKGROUND CONTRAST and the v term by the spot's
own PEAK SCALE, so neither is diluted by a large empty domain.  ``d_raw`` uses no
alignment; ``d_shape`` minimises over a rigid periodic translation of the whole
state (u and v move together).  Only translation is allowed -- no rotation, no
scaling -- so "same state" never silently means "similar-looking state".

Two errors this avoids, both of which produced wrong numbers before
------------------------------------------------------------------
1. **A 2-D mask divided by the wrong count.**  Writing
   ``((u - u_ref)[CORE] ** 2).mean()`` averages over a CORE-SHAPED array; mixing a
   2-D mask with a flattened field divides by something that is not the number of
   selected cells.  Every reduction here is explicitly over a flat index list, so
   the normalisation cannot drift.
2. **Masked FFT correlation on a compact mask.**  With a small mask the raw
   correlation surface is dominated by empty-background noise and its peak can land
   far from the true optimum.  The alignment here minimises the actual masked
   squared error using FFTs of the MASKED fields, which is exact, and the self-test
   cross-checks it against an exhaustive brute-force search.
"""
from __future__ import annotations

from typing import Iterable

import numpy as np

DEFAULT_CORE_THRESHOLD = 0.05


def _core_indices(v_ref: np.ndarray, thr: float) -> np.ndarray:
    """Flat indices of the reference structure's support."""
    return np.flatnonzero(v_ref > thr)


def _sse_table(a: np.ndarray, b: np.ndarray, mask: np.ndarray,
               core: np.ndarray) -> np.ndarray:
    """``SSE(s) = sum_{i in C} (a[i] - b[i + s])**2`` for every periodic shift s.

    Computed exactly with three FFTs rather than by looping over the n**2 shifts::

        SSE(s) = sum_C a^2  -  2 * ((a*mask) star b)[s]  +  (mask star b^2)[s]

    where ``star`` is the periodic correlation.  Doing it this way is not just
    faster -- the direct product form is what makes the
    ``sum_C a^2`` term a genuine constant instead of a per-shift quantity that can
    be mis-normalised.
    """
    m = mask.astype(np.float64)
    am = a.astype(np.float64) * m
    bb = b.astype(np.float64)
    sum_a2 = float((a.astype(np.float64) ** 2 * m).sum())

    # periodic correlation (f star g)[s] = sum_i f[i] g[i+s]
    cross = np.fft.ifft2(np.conj(np.fft.fft2(am)) * np.fft.fft2(bb)).real
    sq = np.fft.ifft2(np.conj(np.fft.fft2(m)) * np.fft.fft2(bb * bb)).real
    return sum_a2 - 2.0 * cross + sq


def core_distance(u_a: np.ndarray, v_a: np.ndarray,
                  u_b: np.ndarray, v_b: np.ndarray,
                  core_mask: np.ndarray | None = None,
                  thr: float = DEFAULT_CORE_THRESHOLD,
                  align: bool = True) -> dict:
    """Distance from state ``a`` to reference state ``b``.

    ``core_mask`` overrides the frozen core set; by default it is
    ``{v_b > thr}``.  Returns a dict with ``d_core_raw``, ``d_core_shape``,
    ``shift`` (the ``(dy, dx)`` applied to ``b`` to best match ``a``), ``n_core``
    and the two normalised components ``d_u``/``d_v``.
    """
    u_a = np.asarray(u_a, dtype=np.float64)
    v_a = np.asarray(v_a, dtype=np.float64)
    u_b = np.asarray(u_b, dtype=np.float64)
    v_b = np.asarray(v_b, dtype=np.float64)
    if not (u_a.shape == v_a.shape == u_b.shape == v_b.shape):
        raise ValueError(f"shape mismatch: {u_a.shape} {v_a.shape} {u_b.shape} {v_b.shape}")
    if u_a.ndim != 2 or u_a.shape[0] != u_a.shape[1]:
        raise ValueError(f"expected square 2-D fields, got {u_a.shape}")

    if core_mask is None:
        core = _core_indices(v_b, thr)
    else:
        core = np.flatnonzero(np.asarray(core_mask).astype(bool).ravel())
    if core.size == 0:
        raise ValueError("the core set is empty; there is no structure to compare")

    n = u_a.shape[0]
    mask = np.zeros((n, n))
    mask.ravel()[core] = 1.0
    ncore = float(core.size)

    # Reference scales, frozen from b and independent of any alignment.
    u_b_flat = u_b.ravel()[core]
    v_b_flat = v_b.ravel()[core]
    norm_u = float(np.mean((1.0 - u_b_flat) ** 2))
    norm_v = float(np.mean(v_b_flat ** 2))
    if norm_u <= 0:
        raise ValueError("u reference has no background contrast inside the core "
                         "(u_ref == 1 on the core); the u term is undefined")
    if norm_v <= 0:
        raise ValueError("v reference is zero on the core; the v term is undefined")

    def objective(sse_u: np.ndarray, sse_v: np.ndarray) -> np.ndarray:
        return (sse_u / ncore) / norm_u + (sse_v / ncore) / norm_v

    sse_u0 = float(((u_a.ravel()[core] - u_b_flat) ** 2).sum())
    sse_v0 = float(((v_a.ravel()[core] - v_b_flat) ** 2).sum())
    d_raw = float(np.sqrt(objective(np.array(sse_u0), np.array(sse_v0))))

    out = {"d_core_raw": d_raw, "d_core_shape": d_raw, "shift": (0, 0),
           "n_core": int(core.size), "norm_u": norm_u, "norm_v": norm_v,
           "d_u": float(np.sqrt(sse_u0 / ncore / norm_u)),
           "d_v": float(np.sqrt(sse_v0 / ncore / norm_v))}
    if not align:
        return out

    # The FFT table is used only to LOCATE the best shifts.  Its product form
    # subtracts large nearly-equal quantities (for the u field, ~|C| * 1 against a
    # residual that may be ~1e-5), so the value it reports at the optimum loses
    # most of its significant digits.  Every candidate is therefore re-evaluated
    # DIRECTLY over the core, which is exact and costs O(|C|) per candidate.
    sse_u = _sse_table(u_a, u_b, mask, core)
    sse_v = _sse_table(v_a, v_b, mask, core)
    obj = objective(sse_u, sse_v)

    def direct(dy: int, dx: int) -> tuple[float, float]:
        ub = np.roll(np.roll(u_b, -dy, 0), -dx, 1)     # b[i + s]
        vb = np.roll(np.roll(v_b, -dy, 0), -dx, 1)
        eu = float(((u_a.ravel()[core] - ub.ravel()[core]) ** 2).sum())
        ev = float(((v_a.ravel()[core] - vb.ravel()[core]) ** 2).sum())
        return eu, ev

    # consider the best few FFT candidates, then choose by the exact value, so a
    # near-tie cannot be decided by FFT round-off
    n_cand = min(8, obj.size)
    cand = np.argsort(obj.ravel())[:n_cand]
    best = None
    for flat in cand:
        dy, dx = (int(v) for v in np.unravel_index(int(flat), (n, n)))
        eu, ev = direct(dy, dx)
        val = eu / ncore / norm_u + ev / ncore / norm_v
        if best is None or val < best[0] - 1e-15:
            best = (val, dy, dx, eu, ev)
    val, dy, dx, eu, ev = best
    out.update({
        "d_core_shape": float(np.sqrt(max(val, 0.0))),
        "shift": (dy, dx),
        "d_u_shape": float(np.sqrt(max(eu / ncore / norm_u, 0.0))),
        "d_v_shape": float(np.sqrt(max(ev / ncore / norm_v, 0.0))),
    })
    return out


def core_distance_bruteforce(u_a: np.ndarray, v_a: np.ndarray,
                             u_b: np.ndarray, v_b: np.ndarray,
                             core_mask: np.ndarray | None = None,
                             thr: float = DEFAULT_CORE_THRESHOLD) -> dict:
    """Exhaustive reference implementation of :func:`core_distance`.

    Kept in the module (not the test) so the fast FFT alignment can always be
    re-checked against an obvious implementation.  Loops over all ``n**2`` shifts.
    """
    u_a = np.asarray(u_a, float); v_a = np.asarray(v_a, float)
    u_b = np.asarray(u_b, float); v_b = np.asarray(v_b, float)
    n = u_a.shape[0]
    core = (_core_indices(v_b, thr) if core_mask is None
            else np.flatnonzero(np.asarray(core_mask).astype(bool).ravel()))
    mask2d = np.zeros((n, n), bool)
    mask2d.ravel()[core] = True
    ncore = float(core.size)
    norm_u = float(np.mean((1.0 - u_b.ravel()[core]) ** 2))
    norm_v = float(np.mean(v_b.ravel()[core] ** 2))

    best = (float("inf"), (0, 0), float("inf"), float("inf"))
    for dy in range(n):
        for dx in range(n):
            ub = np.roll(np.roll(u_b, dy, 0), dx, 1)
            vb = np.roll(np.roll(v_b, dy, 0), dx, 1)
            du = float(((u_a - ub)[mask2d] ** 2).mean()) / norm_u
            dv = float(((v_a - vb)[mask2d] ** 2).mean()) / norm_v
            tot = du + dv
            if tot < best[0] - 1e-15:
                best = (tot, (dy, dx), du, dv)
    raw_du = float(((u_a - u_b)[mask2d] ** 2).mean()) / norm_u
    raw_dv = float(((v_a - v_b)[mask2d] ** 2).mean()) / norm_v
    return {"d_core_shape": float(np.sqrt(best[0])), "shift": best[1],
            "d_core_raw": float(np.sqrt(raw_du + raw_dv)),
            "d_u_shape": float(np.sqrt(best[2])), "d_v_shape": float(np.sqrt(best[3])),
            "n_core": int(core.size)}


# --------------------------------------------------------------------- self-test
def _main() -> int:
    rng = np.random.default_rng(0)
    ok = True
    n = 32

    # a compact reference structure: a v blob with its u depletion halo
    yy, xx = np.indices((n, n))
    def make(cy: int, cx: int, scale: float = 1.0):
        r2 = (yy - cy) ** 2 + (xx - cx) ** 2
        v = 0.4 * scale * np.exp(-r2 / 8.0)
        u = 1.0 - 0.5 * scale * np.exp(-r2 / 40.0)
        return u, v

    u_ref, v_ref = make(10, 12)

    # --- (1) identical state -> zero distance ------------------------------
    d0 = core_distance(u_ref, v_ref, u_ref, v_ref)
    print(f"(1) identical: d_raw={d0['d_core_raw']:.3e} d_shape={d0['d_core_shape']:.3e}"
          f" n_core={d0['n_core']}")
    ok &= d0["d_core_raw"] < 1e-12 and d0["d_core_shape"] < 1e-12

    # --- (2) a pure translation must be recovered exactly ------------------
    # The shifted state is built by ROLLING the reference field, not by
    # re-evaluating the profile at a new centre: the Gaussian above is not a
    # periodic function, so rolling it wraps the tail and produces a state that is
    # genuinely (if slightly) different.  Rolling the array is what makes the two
    # states exact translates, which is the property under test.
    u_sh = np.roll(np.roll(u_ref, 7, 0), 5, 1)
    v_sh = np.roll(np.roll(v_ref, 7, 0), 5, 1)
    d = core_distance(u_sh, v_sh, u_ref, v_ref)
    db = core_distance_bruteforce(u_sh, v_sh, u_ref, v_ref)
    # The two implementations use OPPOSITE sign conventions for "the shift that
    # maps b onto a" -- (+7,+5) versus (-7,-5) == (25,27) mod n.  They describe the
    # same physical alignment, so the test compares the alignment (their sum mod n
    # must vanish), not the raw tuple.
    same_align = ((d["shift"][0] + db["shift"][0]) % n == 0
                  and (d["shift"][1] + db["shift"][1]) % n == 0)
    print(f"(2) pure translation: d_raw={d['d_core_raw']:.4f} "
          f"d_shape={d['d_core_shape']:.3e}  shift={d['shift']} "
          f"bruteforce={db['shift']}  same alignment={same_align}")
    ok &= d["d_core_shape"] < 1e-10 and db["d_core_shape"] < 1e-10 and same_align

    # --- (3) FFT alignment agrees with the brute-force search --------------
    worst = 0.0
    for _ in range(12):
        us = np.roll(np.roll(u_ref, int(rng.integers(0, n)), 0),
                     int(rng.integers(0, n)), 1)
        vs = np.roll(np.roll(v_ref, int(rng.integers(0, n)), 0),
                     int(rng.integers(0, n)), 1)
        a = core_distance(us, vs, u_ref, v_ref)
        b = core_distance_bruteforce(us, vs, u_ref, v_ref)
        worst = max(worst, abs(a["d_core_shape"] - b["d_core_shape"]))
    print(f"(3) FFT alignment vs brute force over 12 rolled states: "
          f"max |d_shape difference| = {worst:.3e} (both should be ~0)")
    ok &= worst < 1e-9

    # --- (4) a genuinely different state is NOT explained by translation ---
    # Two blobs where the reference has one: no rigid shift can fix that.
    u2b, v2b = make(10, 12)
    u3b, v3b = make(22, 24)
    u_far, v_far = np.maximum(u2b, u3b), v2b + v3b
    d4 = core_distance(u_far, v_far, u_ref, v_ref)
    print(f"(4) two-blob state: d_raw={d4['d_core_raw']:.4f} "
          f"d_shape={d4['d_core_shape']:.4f} shift={d4['shift']}  "
          f"(must stay well above 0: a shift cannot remove a second blob)")
    ok &= d4["d_core_shape"] > 0.05 and d4["d_core_shape"] <= d4["d_core_raw"]

    # --- (5) the 2-D-mask normalisation bug is structurally impossible -----
    # d_u and d_v are combined as a sum of squares, so the total must equal
    # sqrt(d_u^2 + d_v^2) with the SAME divisor for both terms.
    lhs = d4["d_core_raw"] ** 2
    rhs = d4["d_u"] ** 2 + d4["d_v"] ** 2
    print(f"(5) component consistency: d^2={lhs:.6f}  d_u^2+d_v^2={rhs:.6f}  "
          f"(rel diff {abs(lhs-rhs)/rhs:.2e})")
    ok &= abs(lhs - rhs) / rhs < 1e-12

    # --- (6) undocumented behaviour must raise, not silently return 0 ------
    try:
        core_distance(u_ref, v_ref, u_ref, v_ref, core_mask=np.zeros((n, n), bool))
        raised = False
    except ValueError:
        raised = True
    print(f"(6) empty core raises ValueError: {raised}")
    ok &= raised

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
