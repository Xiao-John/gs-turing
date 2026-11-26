"""Classic RK4 on a fixed spatial discretisation.

Why this exists next to the explicit-Euler solver
-------------------------------------------------
``core.gs`` steps the spatially discretised system

    dX/dt = F_h(X),      X = (u, v) flattened

with explicit Euler.  A bifurcation bracket found with explicit Euler is a
bracket of *that discrete-time map*, not necessarily of the continuous-time
system on the same grid.  Integrating the SAME ``F_h`` with a 4th-order accurate
step lets a bracket be attributed to the continuous system, and lets the
discretisation error be separated from the time-stepping error.

Contract
--------
``rhs(t, y) -> dy/dt`` with ``y`` a 1-D ``float64`` array.  No clipping, no
positivity projection, no step rejection: a negative concentration is a result to
be reported, not something to hide.
"""
from __future__ import annotations

import math
from typing import Callable, Sequence

import numpy as np

Rhs = Callable[[float, np.ndarray], np.ndarray]


def rk4_step(rhs: Rhs, y: np.ndarray, t: float, dt: float) -> np.ndarray:
    """One classical RK4 step."""
    k1 = np.asarray(rhs(t, y), dtype=np.float64)
    k2 = np.asarray(rhs(t + dt / 2, y + dt / 2 * k1), dtype=np.float64)
    k3 = np.asarray(rhs(t + dt / 2, y + dt / 2 * k2), dtype=np.float64)
    k4 = np.asarray(rhs(t + dt, y + dt * k3), dtype=np.float64)
    return y + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)


def integrate(rhs: Rhs, y0: np.ndarray, t0: float, t1: float, dt: float,
              sample: Sequence[float] | None = None
              ) -> tuple[np.ndarray, np.ndarray]:
    """Integrate from ``t0`` to ``t1``.

    ``t1 - t0`` is rounded UP to a whole number of steps so the endpoint is always
    reached exactly; returning a short trajectory silently would be worse than a
    slightly smaller final ``dt``.

    Returns ``(times, states)`` with ``states[i]`` the state at ``times[i]``.
    When ``sample`` is given, only those times are kept (nearest step), and
    ``t0``/``t1`` are always included.
    """
    y0 = np.array(y0, dtype=np.float64, copy=True)
    span = t1 - t0
    if span < 0:
        raise ValueError(f"t1={t1} precedes t0={t0}")
    if dt <= 0:
        raise ValueError("dt must be positive")
    nsteps = max(1, int(math.ceil(span / dt - 1e-12)))
    h = span / nsteps if nsteps else dt

    wanted = None
    if sample is not None:
        wanted = sorted({float(t0), float(t1), *[float(s) for s in sample]})

    times: list[float] = []
    states: list[np.ndarray] = []
    y = y0
    t = float(t0)

    def maybe_keep(tt: float, yy: np.ndarray) -> None:
        if wanted is None:
            times.append(tt)
            states.append(yy.copy())
            return
        while wanted and abs(wanted[0] - tt) <= 0.5 * h + 1e-12:
            times.append(tt)
            states.append(yy.copy())
            wanted.pop(0)

    maybe_keep(t, y)
    for _ in range(nsteps):
        y = rk4_step(rhs, y, t, h)
        t += h
        maybe_keep(t, y)
    # drop any sample times that fell outside the integrated window
    return np.asarray(times), np.asarray(states)


# --------------------------------------------------------------------- self-test
def _main() -> int:
    # y' = -y, y(0)=1  ->  y(t)=exp(-t).  RK4 local error is O(h^5), global O(h^4),
    # so halving h should cut the error by ~16.
    rhs = lambda t, y: -y                                    # noqa: E731
    T = 2.0
    print("RK4 convergence on y' = -y, y(0)=1, t in [0,2] (exact exp(-t))")
    prev = None
    ratios = []
    ok = True
    for dt in (0.2, 0.1, 0.05, 0.025):
        ts, ys = integrate(rhs, np.array([1.0]), 0.0, T, dt)
        err = abs(ys[-1][0] - math.exp(-T))
        ratio = (prev / err) if prev else float("nan")
        if prev:
            ratios.append(ratio)
        print(f"  dt={dt:<6g} steps={len(ts)-1:<4d} err={err:.3e}  ratio={ratio:.2f}")
        prev = err
    # the last three ratios should all be near 16 (order 4)
    ok &= all(8.0 < r < 32.0 for r in ratios)
    print(f"  order ~4 confirmed: {ok}")

    # the endpoint must be reached exactly, never short
    ts, ys = integrate(rhs, np.array([1.0]), 0.0, 1.0, 0.3)
    exact_end = abs(ts[-1] - 1.0) < 1e-12
    print(f"  endpoint reached exactly with a non-dividing dt: {exact_end}")
    ok &= exact_end

    # sampling keeps exactly the requested instants (plus the endpoints)
    ts, ys = integrate(rhs, np.array([1.0]), 0.0, 1.0, 0.01, sample=[0.25, 0.5])
    print(f"  sampled times = {np.round(ts, 6).tolist()}")
    ok &= set(np.round(ts, 6).tolist()) == {0.0, 0.25, 0.5, 1.0}

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
