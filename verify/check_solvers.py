"""Cross-checks that the two solvers implement the same model.

Everything here is self-contained: the initial condition is generated, not loaded,
so this harness has no dependency on any stored data.

Checks
------
C1  BACKEND PARITY      ``core.solver``'s C kernel and its numpy path produce the
                        same state.  The numpy path is forced in a subprocess via
                        ``GS_NUMPY=1``, because the backend is chosen once at
                        import time.
C2  CROSS-IMPLEMENTATION ``core.gs.FieldSolver(method='euler')`` and
                        ``core.solver.Solver`` agree on the same initial condition
                        with ``resource=uniform(1.0)``.  This is the check that the
                        fast field solver has not drifted from the reference.
C3  IMEX CONVERGENCE    ``method='imex'`` with the 5-point symbol approaches the
                        explicit solution as dt is refined.  This is a CONVERGENCE
                        check, not an equality check: they are different time
                        integrators and at equal dt they are expected to differ.
C4  MASS BALANCE        ``core.solver.mass_balance_residual`` is small.
C5  STABILITY GUARD     an explicit dt above ``0.25*h^2/max(Du,Dv)`` is refused.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parent.parent
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from core import gs as G                                          # noqa: E402
from core import solver as S                                      # noqa: E402

_READY: list[dict] = []


def chk(name: str, ok: bool, detail: str) -> bool:
    _READY.append({"check": name, "pass": bool(ok), "detail": detail})
    print(f"{'PASS' if ok else 'FAIL'}  {name}: {detail}")
    return ok


def seed_state(n: int, seed: int = 7) -> tuple[np.ndarray, np.ndarray]:
    """A small deterministic square seed: u=0.5, v=0.25 in a 14x14 block.

    Deliberately not the classic 96x96 spot file: this harness must be able to
    run on a clean checkout with no stored data at all.
    """
    return S.initial_state(n=n, seed=seed, side=14, u_in=0.5, v_in=0.25,
                           noise=0.005, kind="center_square")


# ------------------------------------------------------------------------ C1
def _run_numpy_backend(n: int, steps: int) -> tuple[np.ndarray, np.ndarray]:
    """Run the same evolution in a subprocess with the numpy backend forced."""
    code = (
        "import sys, numpy as np;"
        f"sys.path.insert(0, {str(REPO)!r});"
        "from core import solver as S;"
        f"u, v = S.initial_state(n={n}, seed=7, side=14, u_in=0.5, v_in=0.25, noise=0.005, kind='center_square');"
        "import numpy as _np;"
        f"s = S.Solver(n={n}, dx=1.0, dt=1.0, Du=0.16, Dv=0.08, f=0.038, k=0.068,"
        "              bc='periodic', u=u, v=v, keep_frames=False, sample_interval=10**9);"
        f"s.step({steps});"
        "print(S.backend());"
        "print(','.join(map(repr, s.u.ravel().tolist())));"
        "print(','.join(map(repr, s.v.ravel().tolist())))"
    )
    env = dict(os.environ, GS_NUMPY="1", GS_NO_REEXEC="1")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, env=env, cwd=str(REPO))
    if out.returncode != 0:
        raise RuntimeError(f"numpy-backend subprocess failed:\n{out.stderr}")
    lines = out.stdout.strip().splitlines()
    backend = lines[0].strip()
    if backend != "numpy":
        raise RuntimeError(f"expected the numpy backend in the subprocess, got {backend!r}")
    u = np.array([float(x) for x in lines[1].split(",")]).reshape(n, n)
    v = np.array([float(x) for x in lines[2].split(",")]).reshape(n, n)
    return u, v


def check_backend_parity(n: int, steps: int) -> None:
    u0, v0 = seed_state(n)
    s = S.Solver(n=n, dx=1.0, dt=1.0, Du=0.16, Dv=0.08, f=0.038, k=0.068,
                 bc="periodic", u=u0, v=v0, sample_interval=10 ** 9)
    s.step(steps)
    u_np, v_np = _run_numpy_backend(n, steps)
    du = float(np.abs(s.u - u_np).max())
    dv = float(np.abs(s.v - v_np).max())
    tol = 1e-12
    chk("C1 backend parity", du < tol and dv < tol,
        f"backend={S.backend()}  max|du|={du:.3e}  max|dv|={dv:.3e}  tol={tol:g}")


# ------------------------------------------------------------------------ C2
def check_cross_implementation(n: int, steps: int, f: float, k: float) -> float:
    """Compare the two independent implementations from the SAME initial state.

    Both start from the seed and run the same number of steps; comparing a state
    against itself after advancing only one of the two (the obvious way to get
    this wrong) measures the evolution, not the implementations.

    f and k are passed explicitly: ``core.solver`` and ``core.gs`` have different
    default f/k, so comparing without pinning them compares two different models.
    """
    u0, v0 = seed_state(n)
    ref = S.Solver(n=n, dx=1.0, dt=1.0, Du=0.16, Dv=0.08, f=f, k=k, bc="periodic",
                   u=u0, v=v0, sample_interval=10 ** 9)
    ref.step(steps)
    g = G.FieldSolver(n=n, h=1.0, dt=1.0, Du=0.16, Dv=0.08, f=f, k=k,
                      u=u0, v=v0, resource=G.uniform(1.0),
                      method="euler", every=10 ** 9, case_id="c2")
    g.step(steps)
    du = float(np.abs(g.u - ref.u).max())
    dv = float(np.abs(g.v - ref.v).max())
    # Both are float64 explicit Euler on the same 5-point periodic stencil, so the
    # only admissible difference is floating-point summation order.  A loose
    # tolerance here would hide a real divergence, so keep it tight.  Guard the
    # comparison against the vacuous case where nothing nucleated.
    live = float(g.v.max()) > 0.05
    tol = 1e-9
    chk("C2 cross-implementation euler", live and du < tol and dv < tol,
        f"core.gs vs core.solver after {steps} steps: max|du|={du:.3e} "
        f"max|dv|={dv:.3e} tol={tol:g} vmax={float(g.v.max()):.4f}")
    return du


# ------------------------------------------------------------------------ C3
def check_imex_convergence(n: int, f: float, k: float) -> None:
    """Show the IMEX/explicit gap shrinking as dt is refined.

    The comparison is at EQUAL dt: both integrators are first order, so both tend
    to the exact solution and their mutual gap must fall roughly linearly with dt.
    Comparing imex(dt) against euler(dt=1) instead would converge to euler's own
    truncation error, not to zero, and would therefore never validate anything.
    """
    u0, v0 = seed_state(n)
    T = 400.0
    errs = []
    for dt in (1.0, 0.5, 0.25):
        steps = int(round(T / dt))
        kw = dict(n=n, h=1.0, dt=dt, Du=0.16, Dv=0.08, f=f, k=k,
                  u=u0, v=v0, resource=G.uniform(1.0), every=10 ** 9)
        e = G.FieldSolver(method="euler", case_id=f"c3e_{dt}", **kw)
        m = G.FieldSolver(method="imex", spectral_lap=False, case_id=f"c3m_{dt}", **kw)
        e.step(steps)
        m.step(steps)
        errs.append((dt, float(np.abs(m.v - e.v).max())))

    detail = "  ".join(f"dt={dt:g}: max|dv|={err:.3e}" for dt, err in errs)
    monotone = all(errs[i + 1][1] < errs[i][1] for i in range(len(errs) - 1))
    ratio = errs[-1][1] / max(errs[0][1], 1e-300)
    # first-order convergence implies dt/4 -> ~0.25 of the dt=1 gap
    ok = monotone and ratio < 0.5
    chk("C3 imex convergence to explicit", ok,
        f"{detail}  (err(dt=0.25)/err(dt=1)={ratio:.3f}, monotone={monotone})")


# ------------------------------------------------------------------------ C4
def check_mass_balance(n: int, f: float, k: float) -> None:
    u0, v0 = seed_state(n)
    s = S.Solver(n=n, dx=1.0, dt=1.0, Du=0.16, Dv=0.08, f=f, k=k,
                 bc="periodic", u=u0, v=v0, sample_interval=10 ** 9)
    s.step(200)                      # let the seed develop a real uv^2 term
    r = S.mass_balance_residual(s, n_steps=1)
    chk("C4 mass balance", r["rel_error"] < 1e-6,
        f"lhs={r['lhs']:.6e}  rhs={r['rhs']:.6e}  rel_err={r['rel_error']:.3e}")


# ------------------------------------------------------------------------ C5
def check_stability_guard(n: int, f: float, k: float) -> None:
    u0, v0 = seed_state(n)
    lim = 0.25 * 1.0 ** 2 / max(0.16, 0.08)
    raised = False
    try:
        G.FieldSolver(n=n, h=1.0, dt=2.0, Du=0.16, Dv=0.08, f=f, k=k,
                      u=u0, v=v0, resource=G.uniform(1.0), method="euler",
                      case_id="c5_bad")
    except ValueError:
        raised = True
    legal = True
    try:
        G.FieldSolver(n=n, h=1.0, dt=1.0, Du=0.16, Dv=0.08, f=f, k=k,
                      u=u0, v=v0, resource=G.uniform(1.0), method="euler",
                      case_id="c5_ok")
    except ValueError:
        legal = False
    chk("C5 stability guard", raised and legal,
        f"bound dt<={lim:.4f}: dt=2.0 refused={raised}, dt=1.0 accepted={legal}")


# --------------------------------------------------------------------------- main
def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--n", type=int, default=96, help="domain size (default 96)")
    ap.add_argument("--steps", type=int, default=300, help="steps for C1/C2")
    ap.add_argument("--f", type=float, default=G.STABLE_SPOT_F)
    ap.add_argument("--k", type=float, default=G.STABLE_SPOT_K)
    ap.add_argument("--json", default=None, help="write the report as JSON here")
    args = ap.parse_args(argv)

    n, f, k = args.n, args.f, args.k
    print(f"Gray-Scott solver checks: n={n} f={f} k={k} steps={args.steps}")
    print(f"core.solver backend = {S.backend()}")

    check_backend_parity(n, args.steps)
    check_cross_implementation(n, args.steps, f, k)
    check_imex_convergence(n, f, k)
    check_mass_balance(n, f, k)
    check_stability_guard(n, f, k)

    npass = sum(1 for r in _READY if r["pass"])
    print(f"\n{npass}/{len(_READY)} checks passed")
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(
            {"n": n, "f": f, "k": k, "backend": S.backend(),
             "checks": _READY, "passed": npass, "total": len(_READY)}, indent=2))
        print(f"wrote {args.json}")
    return 0 if npass == len(_READY) else 2


if __name__ == "__main__":
    sys.exit(main())
