"""Leading eigenpairs of a matrix-free operator, for linear stability.

What this is for
----------------
Given a stationary state ``X*`` of the discretised Gray-Scott system, the linear
stability question is: what is the largest REAL part of the eigenvalues of
``J(X*)``?  A positive real part means the state is unstable, and the associated
eigenvector is the direction in which it escapes.

Two traps this module avoids
----------------------------
1. **Largest real part is not largest modulus.**  Gray-Scott's Jacobian is
   non-symmetric, so a large-modulus eigenvalue can easily be a stable
   fast-decaying mode with a negative real part.  ``which="LR"`` is the default;
   ask for ``"LM"`` only when you actually mean modulus.
2. **A k-step projection is not the k extremal eigenvalues.**  Every returned
   eigenpair carries its explicit residual ``||J w - λ w|| / scale``.  Trust that,
   not the fact that a value appeared in the list.

scipy's ARPACK (``eigs``) does the work when it is available, since it is
restarted and reliable.  Without scipy the module falls back to plain Arnoldi
Ritz values, which are also returned with explicit residuals -- and which the
caller should treat as a rough look rather than converged eigenpairs.
"""
from __future__ import annotations

from typing import Callable

import numpy as np

from numerics.krylov import arnoldi

MatVec = Callable[[np.ndarray], np.ndarray]


def _apply(matvec: MatVec, w: np.ndarray) -> np.ndarray:
    """Apply a REAL operator to a possibly COMPLEX vector.

    A real matrix acting on ``a + i b`` is ``M a + i M b``.  Casting the complex
    eigenvector to float64 instead (which numpy does silently, with only a
    ComplexWarning) throws away the imaginary part of every conjugate pair and
    makes the residual of that pair meaningless -- which is exactly how a
    converged eigenpair gets reported as unconverged.
    """
    if np.iscomplexobj(w) and np.any(w.imag != 0.0):
        return (np.asarray(matvec(w.real), dtype=np.float64)
                + 1j * np.asarray(matvec(w.imag), dtype=np.float64))
    return np.asarray(matvec(np.asarray(w.real, dtype=np.float64)), dtype=np.float64)


def _residuals(matvec: MatVec, vals: np.ndarray, vecs: np.ndarray) -> np.ndarray:
    """Per-eigenpair relative residual ``||J w - λ w|| / max(||J w||, |λ| ||w||)``."""
    out = np.zeros(len(vals))
    for i in range(len(vals)):
        w = vecs[:, i]
        Jw = _apply(matvec, w)
        num = float(np.linalg.norm(Jw - vals[i] * w))
        den = max(float(np.linalg.norm(Jw)), abs(vals[i]) * float(np.linalg.norm(w)),
                  1e-300)
        out[i] = num / den
    return out


def arnoldi_ritz(matvec: MatVec, v0: np.ndarray, k: int = 12
                 ) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Plain Arnoldi Ritz pairs, sorted by descending real part.

    Returns ``(values, vectors, residuals)``.  Cheap and scipy-free, but the
    values are projections, so check the residuals before believing them.
    """
    V, H = arnoldi(matvec, v0, k=k)
    h = H[:H.shape[1], :H.shape[1]]
    vals, svecs = np.linalg.eig(h)
    vecs = V[:, :H.shape[1]] @ svecs
    # normalise so the vectors are comparable
    for i in range(vecs.shape[1]):
        nrm = np.linalg.norm(vecs[:, i])
        if nrm > 0:
            vecs[:, i] /= nrm
    order = np.argsort(-vals.real)
    vals, vecs = vals[order], vecs[:, order]
    return vals, vecs, _residuals(matvec, vals, vecs)


def leading_eigenpairs(matvec: MatVec, n: int, k: int = 6, which: str = "LR",
                       v0: np.ndarray | None = None, tol: float = 1e-10,
                       maxiter: int | None = None
                       ) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
    """``k`` leading eigenpairs of the operator given by ``matvec``.

    ``n`` is the vector length (ARPACK needs it; the matrix-free fallback ignores
    it).  ``which="LR"`` targets the largest real part -- the stability question.

    Returns ``(values, vectors, residuals, method)`` where ``method`` is ``"arpack"``
    or ``"arnoldi"`` so the caller can report how the numbers were obtained.
    """
    if v0 is None:
        rng = np.random.default_rng(0)
        v0 = rng.normal(size=n)
    v0 = np.asarray(v0, dtype=np.float64)

    try:
        import scipy.sparse.linalg as sla

        op = sla.LinearOperator((n, n), matvec=lambda z: np.asarray(matvec(z),
                                                                   dtype=np.float64),
                                dtype=np.float64)
        vals, vecs = sla.eigs(op, k=k, which=which, v0=v0, tol=tol,
                              maxiter=maxiter or 10 * n)
        if np.iscomplexobj(vecs) and not np.any(vecs.imag != 0.0):
            vecs = vecs.real
        order = np.argsort(-vals.real) if which == "LR" else np.argsort(-np.abs(vals))
        vals, vecs = vals[order], vecs[:, order]
        for i in range(vecs.shape[1]):
            nrm = np.linalg.norm(vecs[:, i])
            if nrm > 0:
                vecs[:, i] /= nrm
        return vals, vecs, _residuals(matvec, vals, vecs), "arpack"
    except ImportError:
        vals, vecs, res = arnoldi_ritz(matvec, v0, k=k)
        return vals, vecs, res, "arnoldi"


def stable(values: np.ndarray, tol: float = 1e-8) -> bool:
    """True when no eigenvalue has a positive real part beyond ``tol``."""
    return bool(np.all(np.asarray(values).real <= tol))


# --------------------------------------------------------------------- self-test
def _main() -> int:
    rng = np.random.default_rng(0)
    ok = True

    # --- (1) LR vs LM on a spectrum with a large-modulus STABLE cluster -------
    # This is the trap the module exists to avoid: the dominant eigenvalue by
    # modulus is deep in the left half-plane, so a stability question answered
    # with which="LM" would come back "stable" for an unstable state.
    n = 240
    diag = np.concatenate([[2.5, 1.0], np.linspace(-6.0, -20.0, n - 2)])
    Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    D = Q @ np.diag(diag) @ Q.T                     # symmetric, known spectrum
    A = D + 1.2 * (np.triu(rng.normal(size=(n, n)), 1)
                   - np.triu(rng.normal(size=(n, n)), 1).T)
    truth = np.sort(np.linalg.eigvals(A).real)[::-1]

    vals, vecs, res, method = leading_eigenpairs(lambda z: A @ z, n, k=5, which="LR")
    print(f"method={method}  leading real parts = {np.round(vals.real, 6).tolist()}")
    print(f"                 dense reference     = {np.round(truth[:5], 6).tolist()}")
    print(f"                 per-pair residuals  = {np.round(res, 12).tolist()}")
    err = float(np.max(np.abs(np.sort(vals.real)[::-1] - truth[:5])))
    print(f"  max eigenvalue error = {err:.3e}")
    ok &= err < 1e-6 and float(np.max(res)) < 1e-6

    vals_lm, _, _, _ = leading_eigenpairs(lambda z: A @ z, n, k=2, which="LM")
    print(f"  which='LM' picks real parts {np.round(vals_lm.real, 3).tolist()} "
          f"(|lambda|={np.round(np.abs(vals_lm), 3).tolist()})")
    print(f"  -> 'LR' is required: stable(LR)={stable(vals)}  stable(LM)={stable(vals_lm)}")
    ok &= (not stable(vals)) and stable(vals_lm)

    # --- (2) a genuinely stable operator must be reported stable --------------
    B = D - 30.0 * np.eye(n)
    vals2, _, res2, _ = leading_eigenpairs(lambda z: B @ z, n, k=3, which="LR")
    print(f"  shifted operator leading real parts = {np.round(vals2.real, 3).tolist()}"
          f"  stable={stable(vals2)}  max_residual={float(np.max(res2)):.2e}")
    ok &= stable(vals2) and float(np.max(res2)) < 1e-6

    # --- (3) the scipy-free Arnoldi fallback, on a well-separated operator ----
    # Plain (unrestarted) Arnoldi needs the leading eigenvalues to be reasonably
    # separated; on the clustered operator above it legitimately converges slowly,
    # so it is tested where it is actually applicable.  The point of the check is
    # that it agrees with the dense answer AND reports honest residuals.
    m = 50
    dsep = np.array([3.0, 1.5, 0.2, -2.0, -7.0] + [-25.0] * (m - 5))
    R, _ = np.linalg.qr(rng.normal(size=(m, m)))
    C = R @ np.diag(dsep) @ R.T
    C = C + 0.4 * (np.triu(rng.normal(size=(m, m)), 1)
                   - np.triu(rng.normal(size=(m, m)), 1).T)
    truth_c = np.sort(np.linalg.eigvals(C).real)[::-1][:3]
    va, _, ra = arnoldi_ritz(lambda z: C @ z, rng.normal(size=m), k=45)
    agree = float(np.max(np.abs(np.sort(va.real)[::-1][:3] - truth_c)))
    print(f"  arnoldi fallback vs dense (top 3 real parts): error={agree:.3e} "
          f"residuals[:3]={np.round(ra[:3], 10).tolist()}")
    ok &= agree < 1e-4 and float(np.max(ra[:3])) < 1e-3

    # --- (4) complex conjugate pairs must keep a meaningful residual ---------
    # A rotation-like block has eigenvalues +-i; casting the eigenvector to
    # float64 (the old behaviour) reported these as unconverged.
    G = np.array([[0.0, -1.0], [1.0, 0.0]])
    vc, _vv, rc = arnoldi_ritz(lambda z: G @ z, np.array([1.0, 0.0]), k=2)
    print(f"  rotation block eigenvalues = {np.round(vc, 6).tolist()}  "
          f"residuals={np.round(rc, 12).tolist()}")
    ok &= float(np.max(rc)) < 1e-10

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
