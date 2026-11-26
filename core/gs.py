"""Field solver for Gray-Scott with an explicit resource (supply) field.

Model
-----
    u_t = Du * lap(u) - u*v^2 + f * (u_res(x,y,t) - u)
    v_t = Dv * lap(v) + u*v^2 - (f + k) * v

``u_res == 1`` everywhere reduces this to the plain Gray-Scott model of
:mod:`core.solver`.  The resource field is the ONLY way this module lets a
driver act on the chemistry: gradients are imposed on ``u_res``, never on ``f``.
Changing ``f`` changes both the supply rate and the v wash-out rate, so calling
``f(x,y)`` "food" would be wrong; ``u_res`` has a single, unambiguous meaning.

Two numerical paths, deliberately kept separate and separately labelled
-----------------------------------------------------------------------
``euler``
    Explicit synchronous Euler on the same 5-point periodic Laplacian as
    :mod:`core.solver`.  This is the cross-check, not the ground truth.
``imex``
    One-step IMEX Euler on a periodic domain, solved exactly in Fourier space:

        [1 + dt Du |q|^2 + dt f] u^ = u^ + dt (f u_res^ - uv^2 ^)
        [1 + dt Dv |q|^2 + dt(f+k)] v^ = v^ + dt (uv^2 ^)

    With ``spectral_lap=True`` the symbol is ``-|q|^2`` (true spectral
    diffusion); with ``spectral_lap=False`` it is the 5-point symbol
    ``-4/h^2 [sin^2(qx h/2) + sin^2(qy h/2)]``.  These are different solvers and
    are recorded as such.

.. warning::
   ``dealias=True`` is **not safe for long-time quantitative work**.  The 2/3
   mask truncates the high-wavenumber content of the cubic term ``uv^2``, and the
   resulting ringing appears as a NEGATIVE undershoot that does not shrink when
   ``dt`` is refined -- it is a spatial truncation, so refining time cannot fix
   it.  Measured at ``dt=0.25``, ``t=50``, smooth seed, n=128:

   ==========================  ==================
   configuration               ``vmin`` at t=50
   ==========================  ==================
   spectral=False, dealias=F   ``-5.6e-16``
   spectral=False, dealias=T   ``-2.9e-04``
   spectral=True,  dealias=F   ``-3.5e-07``
   spectral=True,  dealias=T   ``-2.0e-04``
   ==========================  ==================

   The clear default is ``dealias=False``: with the 5-point symbol the scheme is
   then clean to machine precision.  The option is kept so the comparison stays
   possible, and :meth:`FieldSolver._health` will flag a run as unhealthy once the
   undershoot passes the tolerance -- that flag is a true statement about the
   solution, not a nuisance to be tuned away.

Both paths are PERIODIC ONLY.  Non-periodic work belongs in
:class:`core.solver.Solver`, which owns the boundary-condition and wall logic;
this module does not duplicate it.  No clipping, no death threshold, no
artificial source beyond ``u_res``.

Why this file exists next to core/solver.py
-------------------------------------------
``core/solver.py`` is the reference implementation: four boundary rules,
impermeable walls, a compiled C kernel, and a much slower but obvious numpy
path.  This module trades that generality for speed and for a first-class
time-dependent driver field, which is what large parameter sweeps need.  The two
are cross-checked against each other by :mod:`verify.check_solvers`.
"""
from __future__ import annotations

import hashlib
import os
import time
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parent.parent
C_SRC = Path(__file__).resolve().parent / "solver.c"
SOLVER_VERSION = "gs-field 2.0.0"

# Hash ONLY the numerical kernel, so a cosmetic version bump is not mistaken for
# a numerics change (this was a real reproducibility hazard: the same kernel was
# previously reported under three different digests).
CORE_HASH = hashlib.sha256(C_SRC.read_bytes()).hexdigest()[:12]

# Explicit-diffusion stability bound for the 5-point Laplacian in 2D:
#     dt * max(Du, Dv) / h^2 <= 1/4
EXPLICIT_DT_SAFETY = 0.25

# A compact, genuinely STATIONARY spot at Du=0.16, Dv=0.08, nucleated from the
# classic 14x14 Pearson seed (u=0.5, v=0.25 on u=1, v=0).  Measured: Mv=19.84,
# vmax=0.404, Rg=2.95, identical at t=2000, 5000, 10000, 20000 and 40000, so this
# is an equilibrium and not a slow transient.  These values are the reference for
# the "one isolated spot" primitive; see verify/check_solvers.py.
#
# Nearby parameter sets are NOT interchangeable, which is why this is a named
# preset rather than a comment:
#   (0.050, 0.066)  stable to t~20000, then replicates into 16 components
#   (0.060, 0.064)  slowly grows (Mv 39.5 -> 41.5 by t=10000), then fills the domain
#   (0.038, 0.068)  does NOT nucleate at all from this seed -- the seed decays away
#                   by t=200, leaving v == 0
# A decaying seed makes every downstream comparison vacuous (all fields are zero),
# so a check that "passes" on it proves nothing.  Always confirm vmax > 0 first.
STABLE_SPOT_F = 0.055
STABLE_SPOT_K = 0.066


# --------------------------------------------------------------------- resources
class ResourceField:
    """``u_res(x, y, t)``.

    Static fields are stored as an array.  Time-dependent fields are callables
    ``fn(X, Y, t)`` returning an array; they are sampled at the time each step
    actually uses, so a forced switch is never skipped by a coarse dt.
    """

    def __init__(self, kind: str = "uniform", value: float = 1.0, fn=None,
                 array: np.ndarray | None = None, params: dict | None = None):
        self.kind = kind
        self.value = float(value)
        self.fn = fn
        self.array = None if array is None else np.asarray(array, dtype=np.float64)
        self.params = params or {}

    def at(self, X: np.ndarray, Y: np.ndarray, t: float) -> np.ndarray:
        if self.fn is not None:
            a = np.asarray(self.fn(X, Y, t), dtype=np.float64)
        elif self.array is not None:
            a = self.array
        else:
            a = np.full(X.shape, self.value, dtype=np.float64)
        if not np.isfinite(a).all():
            raise ValueError("u_res is not finite")
        if (a < -1e-12).any():
            raise ValueError("u_res must be non-negative (it is a concentration target)")
        return a

    def describe(self) -> dict:
        return {"kind": self.kind, "value": self.value, "params": self.params}


def uniform(value: float = 1.0) -> ResourceField:
    """``u_res = value`` everywhere; ``value=1`` is plain Gray-Scott."""
    return ResourceField("uniform", value)


def sine_gradient(n: int, h: float, A: float, wavelength: float,
                  base: float = 1.0, axis: str = "x") -> ResourceField:
    """``u_res = base + A sin(2 pi x / wavelength)``.  Periodic and smooth."""
    X, Y = np.indices((n, n))
    coord = (X if axis == "y" else Y).astype(np.float64)
    L = n * h
    lam = L if wavelength <= 0 else wavelength

    def fn(Xa, Ya, t, _c=coord, _l=lam):
        return base + A * np.sin(2 * np.pi * _c / _l)
    return ResourceField("sine_gradient", base, fn,
                         params={"A": A, "wavelength": lam, "base": base, "axis": axis})


def tanh_gradient(n: int, h: float, A: float, xc: float, ell: float,
                  base: float = 1.0, axis: str = "x") -> ResourceField:
    """``u_res = base + A tanh((x - xc)/ell)``.

    NON-periodic, therefore valid only on a no-flux / open domain.  This module
    integrates periodic domains only, so a field built here must be used with
    :class:`core.solver.Solver`, or with an ``n`` large enough that the smooth
    step never reaches the seam.
    """
    X, Y = np.indices((n, n))
    coord = (X if axis == "y" else Y).astype(np.float64)

    def fn(Xa, Ya, t, _c=coord):
        return base + A * np.tanh((_c - xc) / ell)
    mean = float((base + A * np.tanh((coord - xc) / ell)).mean())
    return ResourceField("tanh_gradient", mean, fn,
                         params={"A": A, "xc": xc, "ell": ell, "base": base,
                                 "axis": axis, "note": "NON-periodic; no-flux only"})


def periodic_gaussian_band(n: int, h: float, xs0: float, vband: float, w: float,
                           base: float = 1.0, A: float = 0.3,
                           axis: str = "x") -> ResourceField:
    """A Gaussian supply band that moves at speed ``vband`` and wraps periodically."""
    X, Y = np.indices((n, n))
    coord = (X if axis == "y" else Y).astype(np.float64)
    L = n * h

    def fn(Xa, Ya, t, _c=coord, _L=L):
        xs = (xs0 + vband * t) % _L
        d = _c - xs
        d = d - _L * np.round(d / _L)          # wrapped image, smooth at the seam
        return base + A * np.exp(-(d ** 2) / (2 * w * w))
    return ResourceField("periodic_moving_band", base, fn,
                         params={"xs0": xs0, "vband": vband, "w": w, "base": base,
                                 "A": A, "axis": axis})


def from_array(a: np.ndarray, kind: str = "array") -> ResourceField:
    """A static resource field given directly as an array (e.g. a designed mask)."""
    return ResourceField(kind, float(np.mean(a)), array=np.asarray(a, dtype=np.float64))


# ----------------------------------------------------------------------- metrics
def components(a: np.ndarray, thr: float) -> int:
    """4-connected component count of ``{a > thr}``.

    Iterative flood fill, so a large connected blob cannot blow the recursion
    limit.  This is O(N) in cells and is the expensive part of :func:`metrics`.
    """
    m = a > thr
    ny, nx = m.shape
    seen = np.zeros_like(m, bool)
    cnt = 0
    for i in range(ny):
        for j in range(nx):
            if m[i, j] and not seen[i, j]:
                cnt += 1
                st = [(i, j)]
                seen[i, j] = True
                while st:
                    x, y = st.pop()
                    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        p, q = x + dx, y + dy
                        if 0 <= p < ny and 0 <= q < nx and m[p, q] and not seen[p, q]:
                            seen[p, q] = True
                            st.append((p, q))
    return cnt


def metrics(s: "FieldSolver", thr: float = 0.05) -> dict:
    """Scalar summary of one state: mass, peak, support geometry, connectivity.

    ``Rg`` is the v-weighted radius of gyration about the v-weighted centroid,
    both computed on ``{v > thr}``.  A state with no support reports ``None``
    for the shape fields rather than a misleading zero.

    NOTE: ``components`` is a pure-Python flood fill and is far too slow to call
    on every diagnostic sample of a large grid; the T001 protocol drives its own
    sampling and calls this only for end states.
    """
    v, u = s.v, s.u
    ny, nx = s.ny, s.nx
    X, Y = np.indices((ny, nx))
    m = v > thr
    area = int(m.sum())
    out = {
        "t": s.t, "Mv": s.h ** 2 * float(v.sum()), "vmax": float(v.max()),
        "vmin": float(v.min()), "umin": float(u.min()), "umax": float(u.max()),
        "active_area_cells": area, "active_area": area * s.h ** 2,
        "threshold": thr,
        "reaction_flux": s.h ** 2 * float((u * v * v).sum()),
        "resource_target_mean": float(s.ures_now.mean()),
        "resource_target_min": float(s.ures_now.min()),
        "resource_target_max": float(s.ures_now.max()),
    }
    if area > 0:
        w = np.where(m, v, 0.0)
        tot = w.sum()
        cy = float((w * X).sum() / tot)
        cx = float((w * Y).sum() / tot)
        Rg = float(np.sqrt((w * ((X - cy) ** 2 + (Y - cx) ** 2)).sum() / tot))
        out.update({"cy": cy, "cx": cx, "Rg": Rg, "centroid": (cy, cx)})
        # second-moment ratio, for tracking shape change / elongation
        out["elongation"] = float(np.sqrt(
            (w * (X - cy) ** 2).sum() / max((w * (Y - cx) ** 2).sum(), 1e-30)))
    else:
        out.update({"cy": None, "cx": None, "Rg": None, "centroid": None,
                    "elongation": None})
    out["components"] = float(components(v, thr))
    return out


# ------------------------------------------------------------------------ solver
@dataclass
class Frame:
    """One stored sample of the full state."""

    t: float
    v: np.ndarray
    u: np.ndarray
    ures: np.ndarray


class FieldSolver:
    """Periodic Gray-Scott solver with a resource field and two time paths.

    The solver is a plain object: build it, call :meth:`step`, inspect ``u``/``v``,
    optionally :meth:`save`.  It never writes to the ledger; recording a run is
    the runner's job (see :mod:`experiment.runner`), which keeps the numerics free
    of filesystem policy.
    """

    def __init__(self, n: int = 192, h: float = 1.0, dt: float = 1.0,
                 Du: float = 0.16, Dv: float = 0.08, f: float = 0.038, k: float = 0.068,
                 u: np.ndarray | None = None, v: np.ndarray | None = None,
                 resource: ResourceField | None = None,
                 method: str = "euler", spectral_lap: bool = False,
                 dealias: bool = False, every: int = 100, keep_frames: bool = False,
                 defer_record: bool = False, seed: int = 7,
                 case_id: str = "unnamed", worker: str = "core",
                 parent_id: str | None = None, tags: list | None = None,
                 note: str = "", params_extra: dict | None = None,
                 fixed_mask: np.ndarray | None = None,
                 neg_tol: float | None = None,
                 nx: int | None = None, ny: int | None = None,
                 use_c: bool = False):
        if method not in ("euler", "imex"):
            raise ValueError(f"method must be 'euler' or 'imex', got {method!r}")
        self.method = method
        self.spectral_lap = bool(spectral_lap)
        self.dealias = bool(dealias)
        # Explicit rectangular domain.  `n` remains the square shorthand; a
        # non-square grid is REFUSED by the imex path instead of being reshaped.
        if nx is None and ny is None:
            nx = ny = int(n)
        elif nx is None or ny is None:
            raise ValueError(f"give both nx and ny, or neither (got nx={nx}, ny={ny})")
        self.nx, self.ny = int(nx), int(ny)
        if self.nx <= 0 or self.ny <= 0:
            raise ValueError(f"nx and ny must be positive (got {self.nx}, {self.ny})")
        self.n = self.nx                      # square size when nx == ny
        self.h, self.dt = float(h), float(dt)
        # The compiled rectangular kernel is OPT-IN.  Off by default so every
        # previously recorded trajectory keeps running through the same numpy
        # path it was recorded with; a run that uses it says so in its record
        # ("backend": "c-rect") rather than looking identical.
        self.use_c = bool(use_c)
        self.backend = "numpy"
        self.Du, self.Dv, self.f, self.k = Du, Dv, f, k

        if method == "imex" and self.nx != self.ny:
            raise ValueError(
                f"imex is implemented for square grids only; got nx={self.nx}, "
                f"ny={self.ny}.  Use method='euler' on a rectangular domain.")

        # The explicit path is only conditionally stable.  Make a violation a
        # hard error: a run that silently violates it stops early, and its frozen
        # trace has been misread as "the pattern did not move" before.
        if method == "euler":
            dmax = max(self.Du, self.Dv)
            lim = EXPLICIT_DT_SAFETY * self.h ** 2 / dmax if dmax > 0 else float("inf")
            if self.dt > lim + 1e-12:
                raise ValueError(
                    f"explicit dt={self.dt} violates the diffusion bound "
                    f"dt <= 0.25*h^2/max(Du,Dv) = {lim:.6g} for h={self.h}. "
                    f"Use dt<={lim:.6g} or method='imex'.")

        if method == "imex" and dealias:
            # Masks built from sampling points, not from the -|q|^2 symbol.
            kx = np.fft.fftfreq(self.n) * 2 * np.pi / self.h
            ky = np.fft.fftfreq(self.n) * 2 * np.pi / self.h
            KX, KY = np.meshgrid(kx, ky)
            qmax = np.pi / self.h
            self._mask = ((np.abs(KX) <= 2 / 3 * qmax) &
                          (np.abs(KY) <= 2 / 3 * qmax)).astype(np.float64)
        else:
            self._mask = None

        if u is None or v is None:
            u = np.ones((self.ny, self.nx))
            v = np.zeros((self.ny, self.nx))
        self.u = np.array(u, dtype=np.float64, order="C", copy=True)
        self.v = np.array(v, dtype=np.float64, order="C", copy=True)
        if self.u.shape != (self.ny, self.nx) or self.v.shape != (self.ny, self.nx):
            raise ValueError(
                f"u/v shape {self.u.shape}/{self.v.shape} != {(self.ny, self.nx)}")

        # Cells held at u=1, v=0 and re-imposed after every step: a pinned
        # Dirichlet patch (reservoir, wall, or a designed boundary condition).
        if fixed_mask is not None:
            fm = np.asarray(fixed_mask, dtype=np.uint8)
            if fm.shape != (self.ny, self.nx):
                raise ValueError(f"fixed_mask shape {fm.shape} != {(self.ny, self.nx)}")
            self.fixed = fm.reshape(-1).astype(bool)
            self.u[fm.astype(bool)] = 1.0
            self.v[fm.astype(bool)] = 0.0
        else:
            self.fixed = None

        self.resource = resource or uniform(1.0)
        X, Y = np.indices((self.ny, self.nx))
        X = X.astype(np.float64)
        Y = Y.astype(np.float64)
        self._X, self._Y = X, Y
        self.ures_now = self.resource.at(X, Y, 0.0)
        # The C path handles a SCALAR resource level only.  Anything else falls
        # back to the numpy path and says so in the record; it is never silently
        # replaced by a constant.
        self._ures_scalar = float(self.ures_now.min()) if self.ures_now.size else 0.0
        self._ures_uniform = bool(np.all(self.ures_now == self._ures_scalar))
        self._ut = np.empty((self.ny, self.nx), np.float64)
        self._vt = np.empty((self.ny, self.nx), np.float64)
        if self.use_c and self.method == "euler" and self.fixed is None \
                and self._ures_uniform and self.resource.fn is None:
            try:
                import core.solver as _cs
                self._c_evolve = _cs.evolve_rect if _cs.backend() == "c" else None
            except Exception:                      # noqa: BLE001 - report, never guess
                self._c_evolve = None
            if self._c_evolve is not None:
                self.backend = "c-rect"
        else:
            self._c_evolve = None

        self.t = 0.0
        self.every = int(every)
        self.keep_frames = bool(keep_frames)
        self.frames: list[Frame] = []
        self.trace: list[dict] = []
        self.anomalies: list[str] = []
        self.wall = 0.0
        self.steps_done = 0
        self.case_id, self.worker = case_id, worker
        self.parent_id, self.tags, self.note = parent_id, tags or [], note
        self.seed = seed
        self.params_extra = params_extra or {}
        self.defer_record = bool(defer_record)
        # Floor below which a negative concentration counts as a real failure.
        # Measured basis: the dealiased spectral IMEX path accumulates a small
        # negative round-off floor whose magnitude grows with dt and with time --
        # at dt=1 it reaches -8.5e-7 by t=200 while vmax stays a healthy 0.43, i.e.
        # the solution is fine and only the round-off is negative.  The default is
        # therefore set an order of magnitude above that floor, and it is scaled by
        # the field magnitude at check time.  A genuine instability moves the
        # concentration by O(0.01) or more and is still caught.
        self._neg_tol = (float(neg_tol) if neg_tol is not None
                         else 1e-5 * max(1.0, float(dt)))

        # The t=0 sample must describe the state the run actually starts from.
        # When the caller still intends to prepare the fields (shift, seed,
        # composite, ...) it passes defer_record=True and MUST call record_now().
        if not self.defer_record:
            self._record()

    # -- sampling ------------------------------------------------------
    def record_now(self):
        """Discard any sample taken so far and capture the current state as t=0.

        Used after preparation, so frame 0 describes the prepared initial
        condition rather than the raw parent field.
        """
        self.trace = []
        self.frames = []
        self._record()
        return self

    def _record(self):
        self.trace.append(metrics(self))
        if self.keep_frames:
            self.frames.append(Frame(self.t, self.v.copy(), self.u.copy(),
                                     self.ures_now.copy()))

    # -- health --------------------------------------------------------
    def _neg_tolerance(self) -> float:
        """Floor below which a negative concentration is a real failure.

        A bare ``-1e-10`` is the wrong shape for this problem: the FFT paths have a
        round-off floor far above float64 eps.  The floor is scaled by the field
        magnitude so the check stays meaningful at large amplitude, and its base
        value is set from the measurement documented in ``__init__``.
        """
        scale = max(1.0, float(np.abs(self.u).max()), float(np.abs(self.v).max()))
        return self._neg_tol * scale

    def _health(self) -> bool:
        if not np.isfinite(self.u).all() or not np.isfinite(self.v).all():
            self.anomalies.append(f"non-finite at t={self.t}")
            return False
        tol = self._neg_tolerance()
        if self.u.min() < -tol or self.v.min() < -tol:
            self.anomalies.append(
                f"negative concentration at t={self.t}: umin={self.u.min():.3e} "
                f"vmin={self.v.min():.3e} (tol=-{tol:.1e})")
            return False
        if self.v.max() > 5.0 or self.u.max() > 5.0:
            self.anomalies.append(f"overshoot at t={self.t}: vmax={self.v.max():.4f}")
            return False
        return True

    # -- operators -----------------------------------------------------
    def _lap5(self, a: np.ndarray) -> np.ndarray:
        """5-point periodic Laplacian, dx=h."""
        return (np.roll(a, 1, 0) + np.roll(a, -1, 0) +
                np.roll(a, 1, 1) + np.roll(a, -1, 1) - 4.0 * a) / self.h ** 2

    def rhs(self, u: np.ndarray, v: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        """The continuous right-hand side on this grid (used by the numerics layer)."""
        r = u * v * v
        return (self.Du * self._lap5(u) - r + self.f * (self.ures_now - u),
                self.Dv * self._lap5(v) + r - (self.f + self.k) * v)

    # -- one step ------------------------------------------------------
    def _step_euler(self):
        u, v = self.u, self.v
        r = u * v * v
        lu, lv = self._lap5(u), self._lap5(v)
        self.u = u + self.dt * (self.Du * lu - r + self.f * (self.ures_now - u))
        self.v = v + self.dt * (self.Dv * lv + r - (self.f + self.k) * v)

    def _step_imex(self):
        n, h, dt = self.n, self.h, self.dt
        u, v = self.u, self.v
        r = u * v * v
        fu = np.fft.fft2(u)
        fv = np.fft.fft2(v)
        fres = np.fft.fft2(self.ures_now)
        fr = np.fft.fft2(r)
        if self._mask is not None:
            fu, fv, fres, fr = (a * self._mask for a in (fu, fv, fres, fr))
        kx = np.fft.fftfreq(n) * 2 * np.pi / h
        if self.spectral_lap:
            q2 = kx[None, :] ** 2 + kx[:, None] ** 2
        else:
            q2 = (4.0 / h ** 2) * (np.sin(kx[None, :] * h / 2) ** 2 +
                                   np.sin(kx[:, None] * h / 2) ** 2)
        au = 1.0 + dt * self.Du * q2 + dt * self.f
        av = 1.0 + dt * self.Dv * q2 + dt * (self.f + self.k)
        self.u = np.fft.ifft2((fu + dt * (self.f * fres - fr)) / au).real
        self.v = np.fft.ifft2((fv + dt * fr) / av).real

    def step(self, steps: int, record: bool = True) -> bool:
        """Advance ``steps`` iterations.

        Returns False as soon as a health check fails, leaving ``anomalies``
        populated and ``t`` at the last healthy time.  Callers must consult
        :meth:`usable` rather than trusting the end state.

        On the C rectangular path every timestep is screened inside the kernel
        and a rejected step leaves the fields at the last accepted state; the
        kernel's verdict is then cross-checked once per call from numpy, so a
        disagreement between the two is recorded instead of trusted.
        """
        if steps <= 0:
            return True
        if self.anomalies:
            # A failed state is STICKY.  Returning False once and then happily
            # advancing further on the next call let a caller (e.g. a loop of
            # run_until calls) keep integrating a state that had already been
            # declared unhealthy, silently turning a failure into a long trace
            # that looks like a result.  Build a new solver instead.
            return False
        t0 = time.perf_counter()
        if self._c_evolve is not None:
            return self._step_c(steps, record, t0)
        X, Y = self._X, self._Y
        done = 0
        for _ in range(steps):
            # sampled at the time this step actually uses
            self.ures_now = self.resource.at(X, Y, self.t)
            if self.method == "euler":
                self._step_euler()
            else:
                self._step_imex()
            if self.fixed is not None:
                self.u.reshape(-1)[self.fixed] = 1.0
                self.v.reshape(-1)[self.fixed] = 0.0
            self.t += self.dt
            self.steps_done += 1
            done += 1
            if not self._health():
                self.wall += time.perf_counter() - t0
                return False
            if record and done % self.every == 0:
                self._record()
        if record and (done % self.every != 0):
            self._record()
        self.wall += time.perf_counter() - t0
        return True

    def _c_anomaly(self, rep: dict) -> str:
        kind = rep["bad_kind"]
        j, i = divmod(rep["bad_index"], self.nx) if rep["bad_index"] >= 0 else (-1, -1)
        where = (f"cell (j={j}, i={i}) at t={self.t + (rep['bad_step'] + 1) * self.dt:.6g} "
                 f"(step {rep['step_base'] + rep['bad_step'] + 1} of the run)")
        if kind == 1:
            return (f"non-finite candidate at {where}: u={rep['bad_u']!r} v={rep['bad_v']!r}; "
                    f"state left at the last accepted step t={self.t:.6g}")
        if kind == 2:
            return (f"negative concentration at {where}: umin/vmin candidate "
                    f"u={rep['bad_u']:.6e} v={rep['bad_v']:.6e} (tol={-rep['neg_tol']:.3e}); "
                    f"state left at the last accepted step t={self.t:.6g}, nothing clipped")
        return (f"overshoot at {where}: u={rep['bad_u']:.6e} v={rep['bad_v']:.6e} "
                f"(tol={rep['over_tol']:.3e}); state left at the last accepted step "
                f"t={self.t:.6g}")

    def _step_c(self, steps: int, record: bool, t0: float) -> bool:
        """One C call for the whole chunk, with per-timestep screening inside."""
        u, v = self.u, self.v
        if not (u.flags["C_CONTIGUOUS"] and v.flags["C_CONTIGUOUS"]):
            u = np.ascontiguousarray(u)
            v = np.ascontiguousarray(v)
            self.u, self.v = u, v
        neg = self._neg_tolerance()
        rep = self._c_evolve(u, v, self._ut, self._vt, steps=int(steps),
                             dt=self.dt, Du=self.Du, Dv=self.Dv, f=self.f, k=self.k,
                             ures=self._ures_scalar, inv_h2=1.0 / (self.h * self.h),
                             neg_tol=neg, over_tol=5.0)
        rep["step_base"] = self.steps_done
        rep["neg_tol"] = neg
        rep["over_tol"] = 5.0
        accepted = int(rep["steps_done"])
        self.t += accepted * self.dt
        self.steps_done += accepted
        if rep["kind"] != 0:
            self.anomalies.append(self._c_anomaly(rep))
            self.wall += time.perf_counter() - t0
            return False
        # Independent numpy cross-check of the kernel's verdict, once per call.
        # Note this is a SECOND opinion on the same state; it is not the
        # per-step guard (that lives in C and runs every step).
        if not self._health():
            self.anomalies[-1] += " [the C kernel accepted this state; numpy disagrees]"
            self.wall += time.perf_counter() - t0
            return False
        if record:
            self._record()
        self.wall += time.perf_counter() - t0
        return True

    def run_until(self, t_end: float, record: bool = True) -> bool:
        """Advance until model time ``t_end`` (rounded to whole steps).

        Propagates the health verdict; a False return means the state is not usable
        and no further stepping will be performed on this solver.
        """
        if self.anomalies:
            return False
        steps = int(round((t_end - self.t) / self.dt))
        return self.step(steps, record=record)

    # -- output --------------------------------------------------------
    def state(self) -> dict:
        return {"t": self.t, "u": self.u.copy(), "v": self.v.copy(),
                "ures": self.ures_now.copy()}

    def final_metrics(self) -> dict:
        return metrics(self)

    def usable(self, planned_time: float | None = None) -> tuple[bool, str]:
        """Whether this run's end state may be used as a result.

        A health failure stops :meth:`step` early; a bare centroid difference of
        such a run is trivially zero and must not be reported as a measurement.
        """
        if self.anomalies:
            return False, f"anomalies: {self.anomalies[0]}"
        if planned_time is not None and self.t + 1e-9 < planned_time:
            return False, f"stopped at t={self.t} of planned {planned_time}"
        if len(self.trace) < 2:
            return False, "trace has fewer than 2 samples"
        return True, "ok"

    def save(self, results_dir: Path | str, extra: dict | None = None) -> Path:
        """Write the end state (and stored frames) to ``results_dir/<case_id>.npz``.

        Written to a temporary name and atomically renamed, so an interrupted
        save cannot leave a half-written array that later reads as a result.
        """
        results_dir = Path(results_dir)
        results_dir.mkdir(parents=True, exist_ok=True)
        payload = {
            "u": self.u, "v": self.v, "ures": self.ures_now,
            "n": np.int32(self.n), "h": np.float64(self.h), "dt": np.float64(self.dt),
            "nx": np.int32(self.nx), "ny": np.int32(self.ny),
            "backend": np.asarray(self.backend),
            "f": np.float64(self.f), "k": np.float64(self.k),
            "Du": np.float64(self.Du), "Dv": np.float64(self.Dv),
            "t": np.float64(self.t), "method": np.asarray(self.method),
            "core_hash": np.asarray(CORE_HASH),
            "parent_id": np.asarray(self.parent_id or ""),
            "case_id": np.asarray(self.case_id),
        }
        if self.frames:
            payload["frames_v"] = np.asarray([fr.v.astype(np.float32) for fr in self.frames])
            payload["frames_u"] = np.asarray([fr.u.astype(np.float32) for fr in self.frames])
            payload["frames_t"] = np.asarray([fr.t for fr in self.frames])
        if extra:
            for kk, vv in extra.items():
                payload[kk] = vv
        path = results_dir / f"{self.case_id}.npz"
        tmp = results_dir / f".{self.case_id}.tmp.npz"
        np.savez_compressed(tmp, **payload)
        os.replace(tmp, path)
        return path

    def to_record(self, npz_path: Path | str | None = None) -> dict:
        """Build the ledger record for this run (does not write it)."""
        rec = {
            "case_id": self.case_id, "worker": self.worker,
            "status": "completed" if not self.anomalies else "failed",
            "parent_id": self.parent_id, "method": self.method,
            "spectral_lap": self.spectral_lap, "dealias": self.dealias,
            "core_hash": CORE_HASH, "solver_version": SOLVER_VERSION,
            "n": self.n, "h": self.h, "L": self.n * self.h, "dt": self.dt,
            "nx": self.nx, "ny": self.ny,
            "Lx": self.nx * self.h, "Ly": self.ny * self.h,
            "backend": self.backend,
            "Du": self.Du, "Dv": self.Dv, "f": self.f, "k": self.k,
            "seed": self.seed, "t_final": self.t, "steps": self.steps_done,
            "resource": self.resource.describe(),
            "fixed_cells": int(self.fixed.sum()) if self.fixed is not None else 0,
            "final_metrics": self.final_metrics(),
            "anomalies": self.anomalies,
            "wall_seconds": round(self.wall, 4), "tags": self.tags,
            "note": self.note,
        }
        if npz_path is not None:
            rec["npz_path"] = str(npz_path)
        rec.update(self.params_extra)
        return rec
