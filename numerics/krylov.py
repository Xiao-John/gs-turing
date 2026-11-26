"""Matrix-free Krylov tools: restarted GMRES and Arnoldi.

Everything here takes the operator as a CALLABLE ``matvec(x) -> A x``.  No dense
or sparse matrix is ever formed.

Why GMRES and not conjugate gradients
-------------------------------------
The Gray-Scott Jacobian is not symmetric: the reaction block couples u and v
antisymmetrically (``+u v^2`` in one equation, ``-u v^2`` in the other), so the
operator is non-symmetric and CG's convergence theory does not apply.  Restarted
GMRES(m) needs no symmetry assumption.

Why Arnoldi is not "the k rightmost eigenvalues"
------------------------------------------------
A k-step Arnoldi projection gives a k-dimensional approximation of the invariant
subspace, not the k extremal eigenvalues.  Callers must therefore check the
explicit per-eigenpair residual that :func:`numerics.spectrum.leading_eigenpairs`
returns, rather than trusting the projected Ritz values.
"""
from __future__ import annotations

from typing import Callable

import numpy as np

MatVec = Callable[[np.ndarray], np.ndarray]


def gmres(matvec: MatVec, b: np.ndarray, x0: np.ndarray | None = None,
          m: int = 40, tol: float = 1e-9, maxit: int = 200
          ) -> tuple[np.ndarray, dict]:
    """Restarted GMRES(m).

    Returns ``(x, info)`` where ``info`` carries ``converged``, ``iters``,
    ``residual`` (the TRUE residual ``||b - A x||``, recomputed rather than taken
    from the recurrence) and ``residual_history``.
    """
    b = np.asarray(b, dtype=np.float64)
    n = b.size
    x = np.zeros(n) if x0 is None else np.array(x0, dtype=np.float64, copy=True)
    bnorm = float(np.linalg.norm(b))
    if bnorm == 0.0:
        return x, {"converged": True, "iters": 0, "residual": 0.0,
                   "residual_history": [0.0]}

    history: list[float] = []
    total = 0
    outer = max(1, int(np.ceil(maxit / max(1, m))))
    for _ in range(outer):
        r = b - matvec(x)
        beta = float(np.linalg.norm(r))
        history.append(beta / bnorm)
        if beta / bnorm <= tol:
            break

        V = np.zeros((n, m + 1))
        H = np.zeros((m + 1, m))
        cs = np.zeros(m)
        sn = np.zeros(m)
        g = np.zeros(m + 1)
        V[:, 0] = r / beta
        g[0] = beta
        k_used = 0

        for k in range(m):
            total += 1
            w = np.asarray(matvec(V[:, k]), dtype=np.float64)
            for j in range(k + 1):
                H[j, k] = float(np.dot(w, V[:, j]))
                w = w - H[j, k] * V[:, j]
            # one re-orthogonalisation pass: without it the Krylov basis loses
            # orthogonality quickly and the residual recurrence becomes a lie
            for j in range(k + 1):
                corr = float(np.dot(w, V[:, j]))
                H[j, k] += corr
                w = w - corr * V[:, j]
            H[k + 1, k] = float(np.linalg.norm(w))
            if H[k + 1, k] > 1e-14:
                V[:, k + 1] = w / H[k + 1, k]

            # Apply the rotations STORED from previous steps.  Recomputing a
            # rotation from the current column instead (the tempting shortcut)
            # is wrong: each step's rotation must be the same one used to zero
            # that subdiagonal entry earlier, or the triangular factor no longer
            # corresponds to the least-squares problem being solved.
            for j in range(k):
                t = cs[j] * H[j, k] + sn[j] * H[j + 1, k]
                H[j + 1, k] = -sn[j] * H[j, k] + cs[j] * H[j + 1, k]
                H[j, k] = t
            cs[k], sn[k] = _givens(H[k, k], H[k + 1, k])
            H[k, k] = cs[k] * H[k, k] + sn[k] * H[k + 1, k]
            H[k + 1, k] = 0.0
            g[k + 1] = -sn[k] * g[k]
            g[k] = cs[k] * g[k]

            k_used = k + 1
            res = abs(g[k + 1]) / bnorm
            history.append(res)
            if res <= tol:
                break

        y = np.linalg.solve(H[:k_used, :k_used], g[:k_used])
        x = x + V[:, :k_used] @ y
        if abs(g[k_used]) / bnorm <= tol:
            break

    true_res = float(np.linalg.norm(b - matvec(x)) / bnorm)
    return x, {"converged": true_res <= max(tol, 1e-12), "iters": total,
               "residual": true_res, "residual_history": history}


def _givens(a: float, b: float) -> tuple[float, float]:
    """Return ``(c, s)`` with ``[c s; -s c] @ [a, b] = [hypot(a,b), 0]``."""
    r = float(np.hypot(a, b))
    if r == 0.0:
        return 1.0, 0.0
    return a / r, b / r


def arnoldi(matvec: MatVec, v0: np.ndarray, k: int = 12,
            reorth: bool = True) -> tuple[np.ndarray, np.ndarray]:
    """k-step Arnoldi with a modified-Gram-Schmidt basis.

    Returns ``(V, H)`` with ``V`` of shape ``(n, k+1)`` orthonormal columns and
    ``H`` of shape ``(k+1, k)`` upper Hessenberg, satisfying
    ``A V[:, :k] = V H`` up to the residual in row ``k``.
    """
    v0 = np.asarray(v0, dtype=np.float64)
    n = v0.size
    norm = float(np.linalg.norm(v0))
    if norm == 0.0:
        raise ValueError("arnoldi: zero start vector")
    V = np.zeros((n, k + 1))
    H = np.zeros((k + 1, k))
    V[:, 0] = v0 / norm
    for j in range(k):
        w = np.asarray(matvec(V[:, j]), dtype=np.float64)
        for i in range(j + 1):
            H[i, j] = float(np.dot(w, V[:, i]))
            w = w - H[i, j] * V[:, i]
        if reorth:
            for i in range(j + 1):
                corr = float(np.dot(w, V[:, i]))
                H[i, j] += corr
                w = w - corr * V[:, i]
        H[j + 1, j] = float(np.linalg.norm(w))
        if H[j + 1, j] <= 1e-14:
            # Invariant subspace reached at step j.  Column j of H is already
            # filled, so it MUST be returned: truncating to H[:j+1, :j] drops the
            # column that was just computed and hands back a non-square, rank
            # deficient projection whose Ritz values are wrong (for a 2x2 rotation
            # this reported the eigenvalue 0 instead of +-i).  A caller detects the
            # early stop from the returned H being square with j+1 columns.
            return V[:, :j + 1], H[:j + 1, :j + 1]
        V[:, j + 1] = w / H[j + 1, j]
    return V, H


# --------------------------------------------------------------------- self-test
def _main() -> int:
    rng = np.random.default_rng(0)
    ok = True

    # --- GMRES on non-symmetric systems --------------------------------------
    # Both test operators are NON-SYMMETRIC (so a CG-style method would be the
    # wrong tool) but well conditioned.  Conditioning matters for the test to
    # mean anything: restarted GMRES genuinely stalls on an operator with
    # eigenvalues near zero, and a stalled run would be reported as a solver
    # failure when it is really a bad test problem.
    n = 60

    # (a) diagonal + strictly upper perturbation: eigenvalues 1..3, non-symmetric
    A1 = np.diag(np.linspace(1.0, 3.0, n)) + 0.3 * np.triu(rng.normal(size=(n, n)), 1)
    b1 = rng.normal(size=n)
    x1, info1 = gmres(lambda z: A1 @ z, b1, m=30, tol=1e-10)
    exact1 = np.linalg.solve(A1, b1)
    e1 = float(np.linalg.norm(x1 - exact1) / np.linalg.norm(exact1))
    print(f"GMRES (tridiagonal-ish): true residual={info1['residual']:.3e} "
          f"error vs dense solve={e1:.3e}  converged={info1['converged']}  "
          f"matvecs={info1['iters']}")
    ok &= info1["converged"] and e1 < 1e-8

    # (b) lower triangular with a different spectrum, solved from a nonzero guess
    A2 = np.tril(rng.normal(size=(n, n)), -1) + np.diag(np.linspace(2.0, 4.0, n))
    b2 = rng.normal(size=n)
    x2, info2 = gmres(lambda z: A2 @ z, b2, x0=rng.normal(size=n), m=40, tol=1e-10)
    exact2 = np.linalg.solve(A2, b2)
    e2 = float(np.linalg.norm(x2 - exact2) / np.linalg.norm(exact2))
    print(f"GMRES (lower triangular, nonzero x0): residual={info2['residual']:.3e} "
          f"error={e2:.3e}")
    ok &= info2["converged"] and e2 < 1e-8

    # (c) an exactly singular consistency check: b in the range of A
    A3 = np.diag([1.0, 2.0, 3.0, 0.0])
    b3 = np.array([1.0, 2.0, 3.0, 0.0])
    x3, info3 = gmres(lambda z: A3 @ z, b3, m=4, tol=1e-12, maxit=40)
    r3 = float(np.linalg.norm(b3 - A3 @ x3))
    print(f"GMRES (singular, consistent rhs): residual={r3:.3e}")
    ok &= r3 < 1e-9

    # --- Arnoldi orthogonality and Hessenberg relation -----------------------
    M = rng.normal(size=(80, 80))
    V, H = arnoldi(lambda z: M @ z, rng.normal(size=80), k=20)
    orth = float(np.linalg.norm(V.T @ V - np.eye(V.shape[1])))
    k = H.shape[1]
    rel = float(np.linalg.norm(M @ V[:, :k] - V @ H) / np.linalg.norm(M @ V[:, :k]))
    print(f"Arnoldi: ||V^T V - I||={orth:.3e}  ||AV - VH||/||AV||={rel:.3e}  k={k}")
    ok &= orth < 1e-10 and rel < 1e-10

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
