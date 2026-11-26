"""Matrix-free Newton for the stationary problem F(X) = 0.

Purpose
-------
A candidate pattern (a spot, a spot cluster, a would-be "symbol" configuration) is
only a well-defined state if it can be pinned down as a root of the discretised
stationary equations.  Taking a snapshot from a long trajectory gives a state that
is still drifting; a root is reproducible and can be linearised exactly.

Three corrections that matter (each cost a previous attempt real time)
---------------------------------------------------------------------
1. **No ``epsilon * I`` regularisation.**  A periodic Laplacian has a constant null
   vector, which invites "so J is singular, add epsilon I".  J is NOT singular for
   the full reaction-diffusion system: acting on ``(p, q) = (1, 0)`` it returns
   ``(-v^2 - f, +v^2)``, whose norm is order ``f + v^2``, not zero.  A constant
   function is not a spatial translation either.  Adding epsilon I destroys the
   root you were trying to find.
2. **The line search minimises the ORIGINAL residual** ``||F||``, not a
   non-negativity measure.  Damping a step to zero because one far-tail cell went
   slightly negative is what stops Newton from ever converging.
3. **Feasibility is checked only on the ACCEPTED root.**  Intermediate iterates are
   allowed to have either sign.

The solve is via :func:`numerics.krylov.gmres`; no dense Jacobian is formed.
"""
from __future__ import annotations

from typing import Callable

import numpy as np

from numerics.krylov import gmres

Rhs = Callable[[np.ndarray], np.ndarray]
# The Jacobian is a function of the CURRENT iterate: ``jac_matvec(x, z) -> J(x) z``.
# Freezing it at the initial guess (the tempting ``lambda z: J(x0) @ z``) silently
# turns Newton into a quasi-Newton method with a wrong operator, which then fails
# to converge and looks like a Newton bug.
JacMatVec = Callable[[np.ndarray, np.ndarray], np.ndarray]


def newton_krylov(rhs: Rhs, jac_matvec: JacMatVec, x0: np.ndarray,
                  tol: float = 1e-10, maxit: int = 30, gmres_m: int = 40,
                  gmres_tol: float = 1e-8, line_search: bool = True,
                  min_step: float = 1e-10) -> tuple[np.ndarray, dict]:
    """Solve ``F(X) = 0`` from ``x0``.

    Returns ``(x, info)`` with ``info`` containing ``converged``, ``iters``,
    ``residual_history`` (``||F||`` at each accepted iterate), ``accepted``
    (whether the final state is physically feasible, i.e. non-negative) and
    ``message``.
    """
    x = np.array(x0, dtype=np.float64, copy=True)
    F = np.asarray(rhs(x), dtype=np.float64)
    norm0 = max(float(np.linalg.norm(F)), 1e-300)
    history = [float(np.linalg.norm(F))]
    accepted = bool(x.min() >= 0.0)
    message = "maxit reached"
    converged = False

    for _ in range(maxit):
        if history[-1] / norm0 <= tol:
            converged = True
            message = "converged"
            break
        # Newton step: J dx = -F, solved matrix-free.
        dx, ginfo = gmres(lambda z: jac_matvec(x, z), -F, m=gmres_m,
                          tol=gmres_tol, maxit=gmres_m * 8)
        if not np.isfinite(dx).all():
            message = "GMRES produced a non-finite step"
            break

        # Backtracking on the ORIGINAL residual.  This never rejects a step for
        # making some cell negative; only residual growth rejects it.
        alpha = 1.0
        improved = False
        while alpha > min_step:
            trial = x + alpha * dx
            Ft = np.asarray(rhs(trial), dtype=np.float64)
            if not np.isfinite(Ft).all():
                alpha *= 0.5
                continue
            if float(np.linalg.norm(Ft)) < float(np.linalg.norm(F)):
                x, F = trial, Ft
                improved = True
                break
            alpha *= 0.5
        if not improved:
            message = (f"line search exhausted at ||F||={float(np.linalg.norm(F)):.3e}")
            break
        history.append(float(np.linalg.norm(F)))

    if history[-1] / norm0 <= tol:
        converged = True
        message = "converged"
    accepted = bool(x.min() >= 0.0)
    info = {
        "converged": converged,
        "iters": len(history) - 1,
        "residual_history": history,
        "residual": history[-1],
        "relative_residual": history[-1] / norm0,
        "accepted": accepted,
        "message": message,
    }
    return x, info


# --------------------------------------------------------------------- self-test
def _main() -> int:
    rng = np.random.default_rng(0)
    ok = True

    # --- (1) a small nonlinear system with an ANALYTIC Jacobian --------------
    # F(x) = (x0^2 - 4, x1^3 - x0), root (2, 2^(1/3))
    def rhs(x):
        return np.array([x[0] ** 2 - 4.0, x[1] ** 3 - x[0]])

    def jac(x, z):
        return np.array([[2 * x[0], 0.0], [-1.0, 3 * x[1] ** 2]]) @ z

    exact = np.array([2.0, 2.0 ** (1 / 3)])
    root, info = newton_krylov(rhs, jac, np.array([1.0, 1.0]), tol=1e-12, maxit=30)
    err = float(np.linalg.norm(root - exact))
    print(f"(1) nonlinear 2x2: iters={info['iters']} ||F||={info['residual']:.3e} "
          f"err vs exact={err:.3e}  converged={info['converged']}")
    print(f"    residual history: {[f'{v:.2e}' for v in info['residual_history']]}")
    ok &= info["converged"] and err < 1e-9
    h = info["residual_history"]
    quad = len(h) >= 3 and (h[-1] < 1e-6 * h[-2] if h[-2] > 0 else True)
    print(f"    final drop factor: {h[-1]/max(h[-2],1e-300):.2e} (superlinear)")
    ok &= quad

    # --- (2) a periodic nonlinear BVP ---------------------------------------
    # F(u) = D L u - u^3 + 1, solved with the same periodic Laplacian the solver
    # uses.  The Jacobian depends on the CURRENT iterate, which is why the
    # interface takes x as well as the direction.
    n, D = 40, 0.3
    lap = lambda a: (np.roll(a, 1) + np.roll(a, -1) - 2 * a) * n ** 2
    rhs1 = lambda u: D * lap(u) - u ** 3 + 1.0
    jac1 = lambda x, z: D * lap(z) - 3.0 * x ** 2 * z

    u_star, info1 = newton_krylov(rhs1, jac1, 1.0 + 0.1 * rng.normal(size=n),
                                  tol=1e-11, maxit=40)
    res1 = float(np.linalg.norm(rhs1(u_star)))
    print(f"(2) periodic BVP n={n}: iters={info1['iters']} ||F||={res1:.3e} "
          f"accepted={info1['accepted']} min(u)={u_star.min():.4f}")
    ok &= info1["converged"] and res1 < 1e-8
    # grading the residual over the grid is what makes this a real root
    print(f"    pointwise max|F| = {float(np.abs(rhs1(u_star)).max()):.3e}")

    # --- (3) infeasibility is REPORTED, never enforced mid-iteration ---------
    rhs2 = lambda x: np.array([x[0] ** 2 - 1.0])
    jac2 = lambda x, z: np.array([2.0 * x[0]]) * z

    r3, info3 = newton_krylov(rhs2, jac2, np.array([-3.0]), tol=1e-12)
    print(f"(3) negative root: x={r3[0]:.6f} accepted={info3['accepted']} "
          f"||F||={info3['residual']:.2e}  (must converge AND report infeasible)")
    ok &= info3["converged"] and abs(abs(r3[0]) - 1.0) < 1e-9 and not info3["accepted"]

    # --- (4) an unreachable tolerance must fail loudly, not silently ---------
    _, info4 = newton_krylov(rhs2, jac2, np.array([-3.0]), tol=1e-300, maxit=5)
    print(f"(4) impossible tolerance: converged={info4['converged']} "
          f"message={info4['message']!r}")
    ok &= not info4["converged"] and bool(info4["message"])

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
