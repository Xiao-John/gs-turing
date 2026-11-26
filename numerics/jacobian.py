"""Sparse assembly of the Gray-Scott Jacobian.

State ordering
--------------
The state is the flattened 2N-vector ``X = [u.ravel(), v.ravel()]`` of length
``2 n**2``.  The Jacobian is

    J = [[ Du L - diag(v^2) - f I ,      -2 diag(u v)            ],
         [ diag(v^2)              ,  Dv L + 2 diag(u v) - (f+k) I ]]

with ``L`` the SAME 5-point periodic Laplacian the integrator uses (including the
``1/h**2`` scaling), so the operator here is exactly the one the dynamics follows.
It is never densified.

This module needs scipy.  The matrix-free alternatives in
:mod:`numerics.krylov` and :mod:`numerics.spectrum` deliberately do not, so that a
solver-only environment can still linearise a state.
"""
from __future__ import annotations

import numpy as np
import scipy.sparse as sp


def lap_1d(n: int, h: float = 1.0) -> sp.csr_matrix:
    """1-D periodic 5-point stencil ``(a[i-1] - 2 a[i] + a[i+1]) / h**2``."""
    if n < 3:
        raise ValueError("n must be >= 3 for a periodic Laplacian")
    main = -2.0 * np.ones(n)
    off = np.ones(n - 1)
    L = sp.diags([off, main, off], offsets=[-1, 0, 1], format="lil")
    L[0, n - 1] = 1.0
    L[n - 1, 0] = 1.0
    return (L / h ** 2).tocsr()


def laplacian_2d(n: int, h: float = 1.0) -> sp.csr_matrix:
    """2-D periodic 5-point Laplacian on a flattened ``n x n`` field."""
    L = lap_1d(n, h)
    I = sp.identity(n, format="csr")
    return (sp.kron(I, L, format="csr") + sp.kron(L, I, format="csr")).tocsr()


def gs_rhs(u: np.ndarray, v: np.ndarray, h: float, Du: float, Dv: float,
           f: float, k: float, u_res: float | np.ndarray = 1.0
           ) -> tuple[np.ndarray, np.ndarray]:
    """The continuous right-hand side on this grid (periodic, uniform or array u_res)."""
    if np.isscalar(u_res):
        res = np.full(u.shape, float(u_res))
    else:
        res = np.asarray(u_res, dtype=np.float64)
    L = laplacian_2d(u.shape[0], h)
    lap_u = (L @ u.ravel()).reshape(u.shape)
    lap_v = (L @ v.ravel()).reshape(v.shape)
    r = u * v * v
    return (Du * lap_u - r + f * (res - u),
            Dv * lap_v + r - (f + k) * v)


def gs_jacobian_sparse(u: np.ndarray, v: np.ndarray, h: float = 1.0,
                       Du: float = 0.16, Dv: float = 0.08,
                       f: float = 0.055, k: float = 0.066) -> sp.csr_matrix:
    """Sparse Jacobian dF/dX at ``(u, v)``, shape ``(2n^2, 2n^2)``.

    Built for the standard model with ``u_res == 1``; the ``f * u_res`` term is
    constant in the state, so it does not appear in the Jacobian at all.
    """
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    n = u.shape[0]
    if v.shape != (n, n):
        raise ValueError(f"u and v shapes differ: {u.shape} vs {v.shape}")
    N = n * n
    L = laplacian_2d(n, h)
    I = sp.identity(N, format="csr")
    v2 = sp.diags((v * v).ravel(), format="csr")
    uv2 = sp.diags((2.0 * u * v).ravel(), format="csr")

    J_uu = Du * L - v2 - f * I
    J_uv = -uv2
    J_vu = v2
    J_vv = Dv * L + uv2 - (f + k) * I
    return sp.bmat([[J_uu, J_uv], [J_vu, J_vv]], format="csr")


def jacobian_matvec(u: np.ndarray, v: np.ndarray, h: float = 1.0,
                    Du: float = 0.16, Dv: float = 0.08, f: float = 0.055,
                    k: float = 0.066):
    """Return a matrix-free ``matvec`` for the same operator as the sparse form.

    Used to keep :mod:`numerics.newton` and :mod:`numerics.spectrum` usable without
    scipy, and to cross-check the sparse assembly.
    """
    n = u.shape[0]
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    N = n * n

    def lap(a: np.ndarray, hh: float = h) -> np.ndarray:
        return (np.roll(a, 1, 0) + np.roll(a, -1, 0) +
                np.roll(a, 1, 1) + np.roll(a, -1, 1) - 4.0 * a) / hh ** 2

    def matvec(z: np.ndarray) -> np.ndarray:
        p = np.asarray(z, dtype=np.float64).reshape(2, n, n)
        pu, pv = p[0], p[1]
        out_u = Du * lap(pu) - v * v * pu - f * pu - 2.0 * u * v * pv
        out_v = v * v * pu + Dv * lap(pv) + 2.0 * u * v * pv - (f + k) * pv
        return np.concatenate([out_u.ravel(), out_v.ravel()])

    return matvec


# --------------------------------------------------------------------- self-test
def _main() -> int:
    rng = np.random.default_rng(0)
    ok = True
    n, h = 8, 1.0
    Du, Dv, f, k = 0.16, 0.08, 0.055, 0.066

    u = 0.5 + 0.2 * rng.random((n, n))
    v = 0.25 + 0.2 * rng.random((n, n))

    # --- sparse assembly agrees with a finite-difference directional derivative
    J = gs_jacobian_sparse(u, v, h, Du, Dv, f, k)
    print(f"Jacobian: shape={J.shape} nnz={J.nnz} "
          f"(dense would be {(2*n*n)**2} entries)")

    d = rng.normal(size=2 * n * n)
    eps = 1e-6
    X = np.concatenate([u.ravel(), v.ravel()])
    Fp = np.concatenate([a.ravel() for a in gs_rhs(u + eps * d[:n*n].reshape(n, n),
                                                  v + eps * d[n*n:].reshape(n, n),
                                                  h, Du, Dv, f, k)])
    Fm = np.concatenate([a.ravel() for a in gs_rhs(u - eps * d[:n*n].reshape(n, n),
                                                  v - eps * d[n*n:].reshape(n, n),
                                                  h, Du, Dv, f, k)])
    fd = (Fp - Fm) / (2 * eps)
    an = J @ d
    rel = float(np.linalg.norm(fd - an) / max(np.linalg.norm(fd), 1e-30))
    print(f"  sparse J vs finite difference: relative error = {rel:.3e}")
    ok &= rel < 1e-6

    # --- matrix-free matvec agrees with the sparse operator
    mv = jacobian_matvec(u, v, h, Du, Dv, f, k)
    rel2 = float(np.linalg.norm(mv(d) - an) / max(np.linalg.norm(an), 1e-30))
    print(f"  matrix-free matvec vs sparse J: relative error = {rel2:.3e}")
    ok &= rel2 < 1e-12

    # --- the Laplacian annihilates constants (a real invariant, not a tolerance)
    L = laplacian_2d(n, h)
    const = np.ones(n * n)
    print(f"  ||L @ 1|| = {float(np.linalg.norm(L @ const)):.3e} (must be ~0)")
    ok &= float(np.linalg.norm(L @ const)) < 1e-12

    # --- at v = 0 the reaction coupling vanishes, so J must be block diagonal:
    # the two species decouple and each reduces to a pure linear operator.  This
    # is a structural property of the model, not a tolerance question.
    u0 = np.ones((n, n))
    v0 = np.zeros((n, n))
    J0 = gs_jacobian_sparse(u0, v0, h, Du, Dv, f, k)
    p = rng.normal(size=(n, n))
    q = rng.normal(size=(n, n))
    z = np.concatenate([p.ravel(), q.ravel()])
    got = J0 @ z
    L = laplacian_2d(n, h)
    want = np.concatenate([(Du * (L @ p.ravel()) - f * p.ravel()),
                           (Dv * (L @ q.ravel()) - (f + k) * q.ravel())])
    err0 = float(np.linalg.norm(got - want) / np.linalg.norm(want))
    cross = float(np.abs(J0[:n * n, n * n:]).max())
    print(f"  v=0 decoupling: rel err vs block-diagonal linear form = {err0:.3e}, "
          f"max|J_uv| = {cross:.3e}")
    ok &= err0 < 1e-12 and cross == 0.0

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
