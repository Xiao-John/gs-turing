"""Reference Gray-Scott solver: boundary conditions, walls, two backends.

Single-owner module.  Everything else imports this; nobody forks their own solver.
For a faster periodic-only solver with a time-dependent resource field, see
:mod:`core.gs`.

Model
-----
    u_t = Du * lap(u) - u*v^2 + f*(1-u)
    v_t = Dv * lap(v) + u*v^2 - (f+k)*v

5-point Laplacian, explicit Euler, synchronous update (u_new and v_new both use
the old fields), float64, no clipping / death threshold / noise source.

Backends
--------
`backend()` returns ``"c"`` when the C kernel compiled, else ``"numpy"``.
Both implement the same discrete update; :mod:`verify.check_solvers` checks them
against each other and against the closed-form mass-balance invariant.

Scope
-----
This is the general solver: four boundary rules (periodic, noflux, reservoir,
dirichlet), impermeable walls via an ``active`` mask, and heterogeneous
parameter fields.  It has no resource/supply driver field; that lives in
:mod:`core.gs`.
"""
from __future__ import annotations

import ctypes
import hashlib
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parent
C_SRC = ROOT / "solver.c"
C_LIB = ROOT / ("_solver.dylib" if sys.platform == "darwin" else "_solver.so")
SOLVER_VERSION = "gs-core 1.1.0"

# The bundled DSH runtime ships a hardened+library-validated interpreter that
# refuses to dlopen this project's ad-hoc-signed C kernel.  If a project venv
# exists, transparently re-exec into it so workers get the fast kernel.
_VENV = ROOT.parent / ".venv" / "bin" / "python"
if (_VENV.exists() and os.environ.get("GS_NO_REEXEC") != "1"
        and not os.environ.get("GS_REEXEC")
        and Path(sys.executable).resolve() != _VENV.resolve()
        and "-c" not in sys.argv[:1] and sys.argv and not sys.argv[0].startswith("-")):
    os.execve(str(_VENV), [str(_VENV), *sys.argv], dict(os.environ, GS_REEXEC="1"))



# --------------------------------------------------------------------------
# kernel loading
# --------------------------------------------------------------------------
def _lib_hash() -> str:
    """Hash ONLY the numerical kernel.

    The first three revisions mixed the version string into this digest, so a
    cosmetic version bump looked like a numerics change and made a mid-session
    core update look like a reproducibility hazard.  The kernel is byte
    identical across gs-core 1.0.0/1.0.1/1.0.2 (md5 758b9b9a98ecc0bfd83177b166c54228);
    this hash now says so.
    """
    return hashlib.sha256(C_SRC.read_bytes()).hexdigest()[:12]


def _build() -> ctypes.CDLL | None:
    if os.environ.get("GS_NUMPY"):
        return None
    if not C_LIB.exists() or C_LIB.stat().st_mtime < C_SRC.stat().st_mtime:
        try:
            subprocess.run(
                ["cc", "-O3", "-shared", "-fPIC", str(C_SRC), "-o", str(C_LIB)],
                check=True, capture_output=True,
            )
        except (OSError, subprocess.CalledProcessError):
            return None
    # macOS hardened runtime: the freshly compiled dylib is unsigned, so an
    # interpreter that enforces library validation cannot map it.  Ad-hoc sign
    # it, then load; a runtime without validation also accepts the signed file.
    if sys.platform == "darwin":
        try:
            subprocess.run(["codesign", "-f", "-s", "-", str(C_LIB)],
                           check=True, capture_output=True)
        except (OSError, subprocess.CalledProcessError):
            pass
    try:
        lib = ctypes.CDLL(str(C_LIB))
    except OSError:
        return None
    d = np.ctypeslib.ndpointer(dtype=np.float64, flags="C_CONTIGUOUS")
    i = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
    b = np.ctypeslib.ndpointer(dtype=np.uint8, flags="C_CONTIGUOUS")
    lib.gs_evolve.argtypes = [d, d, d, d, i, b, ctypes.c_int, ctypes.c_long,
                              ctypes.c_double, ctypes.c_double, ctypes.c_double,
                              ctypes.c_double, ctypes.c_double, ctypes.c_int, b, d, d]
    lib.gs_evolve.restype = ctypes.c_int
    lib.gs_probe.argtypes = [d, d, ctypes.c_int, d]
    lib.gs_probe.restype = ctypes.c_int

    # Rectangular periodic kernel (nx x ny, scalar resource level).  Same file,
    # same compile command, same hash as the square kernel above; it exists so a
    # rectangular physical domain can run in the main toolchain instead of being
    # squashed into (n, n) or moved to a private solver.
    class _RectReport(ctypes.Structure):
        _fields_ = [("steps_done", ctypes.c_long), ("bad_step", ctypes.c_long),
                    ("bad_kind", ctypes.c_int), ("bad_index", ctypes.c_long),
                    ("bad_u", ctypes.c_double), ("bad_v", ctypes.c_double)]

    lib._RectReport = _RectReport          # keep the type alive with the library
    lib.gs_evolve_rect.argtypes = [
        d, d, d, d, ctypes.c_int, ctypes.c_int, ctypes.c_long,
        ctypes.c_double, ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.c_double, ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.c_double, ctypes.POINTER(_RectReport)]
    lib.gs_evolve_rect.restype = ctypes.c_int
    return lib


_LIB = _build()
CORE_HASH = _lib_hash()


def backend() -> str:
    return "c" if _LIB is not None else "numpy"


def evolve_rect(u, v, ut, vt, *, steps: int, dt: float, Du: float, Dv: float,
                f: float, k: float, ures: float, inv_h2: float,
                neg_tol: float = 1e-10, over_tol: float = 5.0) -> dict:
    """Advance a rectangular periodic GS state in place with the C kernel.

    ``(u, v)`` are ``(ny, nx)`` C-contiguous float64 and are updated only for
    accepted steps; ``(ut, vt)`` is caller-owned scratch of the same shape.  The
    resource level is the scalar ``ures`` and ``inv_h2 = 1/h**2`` scales the raw
    5-point stencil, so ``Du``/``Dv`` keep their physical meaning.

    The kernel screens EVERY timestep (non-finite, below ``-neg_tol``, above
    ``over_tol``).  A rejected step leaves ``(u, v)`` exactly at the last
    accepted state: nothing is advanced, nothing is clipped, and the returned
    ``bad_kind`` / ``bad_index`` / ``bad_u`` / ``bad_v`` say why.
    """
    if _LIB is None:
        raise RuntimeError("the C kernel is not available (backend()=='numpy')")
    if u.shape != v.shape or u.shape != ut.shape or u.shape != vt.shape:
        raise ValueError("u, v, ut, vt must share one (ny, nx) shape")
    ny, nx = u.shape
    for a in (u, v, ut, vt):
        if a.dtype != np.float64 or not a.flags["C_CONTIGUOUS"]:
            raise ValueError("u, v, ut, vt must be C-contiguous float64")
    rep = _LIB._RectReport()
    kind = _LIB.gs_evolve_rect(u, v, ut, vt, int(nx), int(ny), int(steps),
                               float(Du), float(Dv), float(f), float(k), float(dt),
                               float(ures), float(inv_h2), float(neg_tol),
                               float(over_tol), rep)
    return {"kind": int(kind), "steps_done": int(rep.steps_done),
            "bad_step": int(rep.bad_step), "bad_kind": int(rep.bad_kind),
            "bad_index": int(rep.bad_index), "bad_u": float(rep.bad_u),
            "bad_v": float(rep.bad_v)}


# --------------------------------------------------------------------------
# finite difference operators
# --------------------------------------------------------------------------
def laplacian(a: np.ndarray, bc: str = "periodic") -> np.ndarray:
    """Reference 5-point Laplacian, dx=1.  Slow but obviously correct."""
    if bc == "periodic":
        return (np.roll(a, 1, 0) + np.roll(a, -1, 0)
                + np.roll(a, 1, 1) + np.roll(a, -1, 1) - 4.0 * a)
    p = np.pad(a, 1, mode="edge")          # no-flux / dirichlet neighbour rule
    return (p[2:, 1:-1] + p[:-2, 1:-1] + p[1:-1, 2:] + p[1:-1, :-2] - 4.0 * a)


def diffusive_dt_limit(Du: float = 0.16, Dv: float = 0.08, dx: float = 1.0) -> float:
    """Explicit-diffusion stability bound ``dt * max(D) / dx**2 <= 1/4``."""
    return 0.25 * dx * dx / max(Du, Dv)


# --------------------------------------------------------------------------
# geometry
# --------------------------------------------------------------------------
_GEOM_CACHE: dict[tuple, tuple[np.ndarray, np.ndarray]] = {}


def geometry(n: int, bc: str = "periodic", mask: np.ndarray | None = None):
    """Return (neighbour_table, active).

    neighbour_table[n*i+j] = 4 cell indices [down, up, right, left] already
    resolved for the boundary rule and for impermeable walls.
    active = 1 for reacting cells, 0 for walls / masked-out cells.
    """
    key = (n, bc, None if mask is None else hashlib.sha1(np.ascontiguousarray(mask).tobytes()).hexdigest())
    if key in _GEOM_CACHE:
        return _GEOM_CACHE[key]

    active = np.ones((n, n), np.uint8) if mask is None else mask.astype(np.uint8)
    ys, xs = np.indices((n, n))
    flat = np.arange(n * n, dtype=np.int64).reshape(n, n)
    self_flat = np.arange(n * n, dtype=np.int64).reshape(n, n)
    nb = np.empty((n, n, 4), np.int32)
    for arm, (dy, dx_) in enumerate(((1, 0), (-1, 0), (0, 1), (0, -1))):
        y = ys + dy
        x = xs + dx_
        if bc == "periodic":
            y %= n
            x %= n
        else:
            y = np.clip(y, 0, n - 1)
            x = np.clip(x, 0, n - 1)
        q = self_flat[y, x]
        q = np.where(active[y, x] == 1, q, flat)   # neighbour inside a wall -> self
        nb[..., arm] = q.reshape(n, n).astype(np.int32)
    nb = np.ascontiguousarray(nb.reshape(n * n, 4))
    _GEOM_CACHE[key] = (nb, active)
    return nb, active


# --------------------------------------------------------------------------
# initial conditions
# --------------------------------------------------------------------------
def initial_state(n: int = 96, seed: int = 7, loc: tuple[int, int] | None = None,
                  side: int = 14, u_in: float = 0.5, v_in: float = 0.25,
                  noise: float = 0.005, kind: str = "center_square",
                  background_u: float = 1.0, bc: str = "periodic",
                  **kw) -> tuple[np.ndarray, np.ndarray]:
    """Default seed: u=1, v=0 everywhere, a central 14x14 block
    u=.5, v=.25, independent uniform [-noise, +noise] on each field.
    u noise is drawn first, then v noise, from one default_rng(seed)."""
    u = np.full((n, n), float(background_u))
    v = np.zeros((n, n))
    rng = np.random.default_rng(seed)
    cy, cx = loc if loc is not None else (n // 2, n // 2)
    h = side // 2
    lo, hi = side - side // 2, side // 2      # exactly `side` cells, odd sides included

    def block(y0: int, x0: int, s: int):
        """Top-left-anchored block of exactly s x s cells, clamped to the domain.

        Three bugs lived here.  (1) An odd `side` produced a (side-1)-cell slice
        (fixed in 1.0.2).  (2) A top-left running off the low edge produced an
        EMPTY slice that failed to broadcast, which made a distance scan look
        like a seed-size effect.  (3) Clamping the
        seed ONTO the reservoir frame silently overwrote the frame, turning a
        rim-quenched initial condition into a fresh nucleus at the boundary --
        so a seed whose nearest cell would land inside the frame is now moved
        inward until it clears it, and never overlaps the fixed border.
        """
        lo_b, hi_b = (1, n - 1) if bc in ("reservoir",) else (0, n)
        span = hi_b - lo_b
        if s > span:
            raise ValueError(
                f"seed side {s} does not fit inside the active interior "
                f"[{lo_b},{hi_b}) of an n={n} {bc} domain")
        y0 = max(lo_b, min(int(y0), hi_b - s))
        x0 = max(lo_b, min(int(x0), hi_b - s))
        return (slice(y0, y0 + s), slice(x0, x0 + s))

    if kind == "center_square":
        sl = block(cy - lo, cx - lo, side)
        u[sl] = u_in + rng.uniform(-noise, noise, (side, side))
        v[sl] = v_in + rng.uniform(-noise, noise, (side, side))
    elif kind == "disk":
        r = side / 2.0
        yy, xx = np.indices((n, n))
        m = (yy - cy) ** 2 + (xx - cx) ** 2 <= r * r
        a = rng.uniform(-noise, noise, (n, n))
        b = rng.uniform(-noise, noise, (n, n))
        u[m] = u_in + a[m]
        v[m] = v_in + b[m]
    elif kind == "stripes":
        sl = block(cy - lo, 0, 1)
        cols = block(0, cx - lo, side)[1]
        u[:, cols] = u_in + rng.uniform(-noise, noise, (n, side))
        v[:, cols] = v_in + rng.uniform(-noise, noise, (n, side))
    elif kind == "multi_seed":
        pts = kw.get("points", [(n // 4, n // 4), (3 * n // 4, 3 * n // 4)])
        for (py, px) in pts:
            sl = block(py - lo, px - lo, side)
            u[sl] = u_in + rng.uniform(-noise, noise, (side, side))
            v[sl] = v_in + rng.uniform(-noise, noise, (side, side))
    elif kind == "random_field":
        amp = kw.get("amplitude", 0.25)
        u = np.clip(0.5 + rng.uniform(-amp, amp, (n, n)), 0.0, 1.0)
        v = np.clip(0.25 + rng.uniform(-amp, amp, (n, n)), 0.0, 1.0)
        on = rng.random((n, n)) < kw.get("density", 0.5)
        u[~on] = 1.0
        v[~on] = 0.0
    elif kind == "uniform_spots":
        # sparse small seeds on a jittered lattice
        count = kw.get("count", 8)
        for _ in range(count):
            py = int(rng.integers(0, n))
            px = int(rng.integers(0, n))
            yy, xx = np.indices((n, n))
            m = (yy - py) ** 2 + (xx - px) ** 2 <= h * h
            u[m] = u_in
            v[m] = v_in
    else:
        raise ValueError(f"unknown initial kind {kind!r}")
    return u, v


def clone_field(u: np.ndarray, v: np.ndarray, scale: float = 1.0,
                conserve: bool = True) -> tuple[np.ndarray, np.ndarray]:
    """Scale the V field.  conserve=True keeps the V integral fixed."""
    w = v * scale
    if conserve:
        s0, s1 = v.sum(), w.sum()
        if s1 > 0:
            w = w * (s0 / s1)
    return u.copy(), w


# --------------------------------------------------------------------------
# the runner
# --------------------------------------------------------------------------
@dataclass
class RunResult:
    u: np.ndarray
    v: np.ndarray
    times: np.ndarray
    frames: np.ndarray          # (n_frames, n, n) float32 of v, if arrays kept
    trace: dict[str, np.ndarray]
    diagnostics: dict[str, Any] = field(default_factory=dict)


class Solver:
    """Stateful runner with a single configuration.

    step() advances model time and records metrics + optional v frames.
    Intervention is done by mutating u/v directly through the public fields.
    """

    def __init__(self, n: int = 96, dx: float = 1.0, dt: float = 1.0,
                 Du: float = 0.16, Dv: float = 0.08, f: float = 0.035, k: float = 0.065,
                 bc: str = "periodic", mask: np.ndarray | None = None,
                 u: np.ndarray | None = None, v: np.ndarray | None = None,
                 seed: int = 7, keep_frames: bool = False,
                 sample_interval: int = 100, param_field: dict | None = None,
                 fixed_mask: np.ndarray | None = None):
        if bc not in ("periodic", "noflux", "reservoir", "dirichlet"):
            raise ValueError(bc)
        self.n, self.dx, self.dt = n, dx, dt
        self.Du, self.Dv, self.f, self.k = Du, Dv, f, k
        self.bc, self.seed = bc, seed
        self.sample_interval = sample_interval
        self.keep_frames = keep_frames
        if u is None or v is None:
            u, v = initial_state(n, seed)
        # ALWAYS take a private copy.  np.ascontiguousarray does NOT copy an array
        # that is already C-contiguous float64, so the old version aliased the
        # caller's arrays.  The Solver updates u/v in place (np.add(..., out=...)
        # and the C kernel writes through persistent views), so an alias meant two
        # Solvers built from the same arrays silently shared one state -- and a
        # "cross-implementation" comparison between them measured nothing.  The
        # symptom is nasty: the disagreement appears and disappears depending on
        # how many solvers the process happens to have constructed.
        self.u = np.array(u, dtype=np.float64, order="C", copy=True)
        self.v = np.array(v, dtype=np.float64, order="C", copy=True)
        self.nb, self.active = geometry(n, bc, mask)
        self.mask = self.active.copy()
        # Dirichlet reservoirs: an explicit set of cells held at u=1, v=0 and
        # overwritten after every update.  Without a fixed mask, bc="dirichlet"
        # degenerates to bc="noflux"; that equivalence is now impossible to
        # reach silently because the mask is recorded and reported.
        if fixed_mask is not None:
            self.fixed = np.ascontiguousarray(fixed_mask.astype(np.uint8)).reshape(-1)
        else:
            self.fixed = np.zeros(n * n, np.uint8)
        if bc == "dirichlet" and not self.fixed.any():
            self.anomalies_note = (
                "bc=dirichlet with an empty fixed mask behaves exactly like noflux")
        self.u[self.active == 0] = 1.0
        self.v[self.active == 0] = 0.0
        if bc == "reservoir":
            self._pin_frame()
        fx = self.fixed.reshape(n, n) == 1
        if fx.any():
            self.u[fx] = 1.0
            self.v[fx] = 0.0
        # heterogeneous parameter fields: f, k, Du, Dv may be arrays
        self.param_field = param_field or {}
        self.t = 0.0
        self._ut = np.empty(n * n, np.float64)
        self._vt = np.empty(n * n, np.float64)
        self._u_flat = self.u.reshape(-1)
        self._v_flat = self.v.reshape(-1)
        self.frames: list[np.ndarray] = []
        self.trace = {"time": [], "mass": [], "max_v": [], "mean_v": [], "std_v": []}
        self.anomalies: list[str] = []
        self.wall = 0.0
        self._record(force=True)

    # -- helpers ---------------------------------------------------------
    def _pin_frame(self):
        self.u[[0, -1], :] = 1.0
        self.u[:, [0, -1]] = 1.0
        self.v[[0, -1], :] = 0.0
        self.v[:, [0, -1]] = 0.0

    def _record(self, force: bool = False):
        v = self.v
        self.trace["time"].append(self.t)
        self.trace["mass"].append(float(v.sum()) * self.dx * self.dx)
        self.trace["max_v"].append(float(v.max()))
        self.trace["mean_v"].append(float(v.mean()))
        self.trace["std_v"].append(float(v.std()))
        if self.keep_frames:
            self.frames.append(v.astype(np.float32))

    def _check(self):
        u, v = self.u, self.v
        if not np.isfinite(u).all() or not np.isfinite(v).all():
            self.anomalies.append(f"non-finite at t={self.t}")
            return False
        uu = u[self.active == 1]
        vv = v[self.active == 1]
        # Scale-relative floor, for the same reason as core.gs: an absolute
        # -1e-10 rejects round-off rather than detecting instability.
        scale = max(1.0, float(np.abs(uu).max()) if uu.size else 1.0,
                    float(np.abs(vv).max()) if vv.size else 1.0)
        tol = 1e-8 * scale
        if uu.min() < -tol or vv.min() < -tol:
            self.anomalies.append(
                f"negative concentration at t={self.t}: min u={uu.min():.3e} "
                f"min v={vv.min():.3e} (tol=-{tol:.1e})")
            return False
        if uu.max() > 1.5 or vv.max() > 5.0:
            self.anomalies.append(
                f"overshoot at t={self.t}: max u={uu.max():.4f} max v={vv.max():.4f}")
            return False
        return True

    def _substep_params(self):
        """Return (f_field, k_field, Du_field, Dv_field) or None when uniform."""
        pf = self.param_field
        if not pf:
            return None
        return pf

    # -- evolution -------------------------------------------------------
    def step(self, steps: int, record: bool = True) -> bool:
        """Advance `steps` Euler iterations of size dt (= physical time steps*dt).

        Metrics are sampled every `sample_interval` iterations; v frames are
        stored at the same instants when keep_frames is on.
        """
        if steps <= 0:
            return True
        if self.anomalies:
            # sticky: an unhealthy state must not be advanced further (see core.gs)
            return False
        t0 = time.perf_counter()
        pf = self._substep_params()
        if pf is None:
            remaining = steps
            while remaining > 0:
                chunk = min(remaining, self.sample_interval)
                self._advance(chunk)
                # The C kernel pins an outer reservoir frame internally; an
                # internal Dirichlet patch (e.g. a fixed patch of fresh medium in
                # the middle of a domain) needs the same re-imposition.
                if self.fixed.any():
                    self._reimpose()
                self.t += chunk * self.dt
                remaining -= chunk
                if record:
                    self._record()
                if not self._check():
                    self.wall += time.perf_counter() - t0
                    return False
            self.wall += time.perf_counter() - t0
            return True
        # heterogeneous parameter fields: single Euler steps on the numpy path
        done = 0
        for _ in range(steps):
            self._advance_hetero(pf)
            self.t += self.dt
            done += 1
            if not self._check():
                if record:
                    self._record()
                self.wall += time.perf_counter() - t0
                return False
            if done % self.sample_interval == 0 and record:
                self._record()
        if record and done % self.sample_interval != 0:
            self._record()
        self.wall += time.perf_counter() - t0
        return True

    def _advance(self, steps: int):
        if _LIB is not None and self.dt * max(self.Du, self.Dv) / (self.dx ** 2) <= 0.25:
            bc_mode = {"periodic": 0, "noflux": 1, "reservoir": 2, "dirichlet": 3}[self.bc]
            _LIB.gs_evolve(self._u_flat, self._v_flat, self._ut, self._vt,
                           self.nb, self.active.reshape(-1), self.n, int(steps),
                           self.Du / (self.dx ** 2), self.Dv / (self.dx ** 2),
                           self.f, self.k, self.dt, bc_mode, self.fixed,
                           self._u_flat, self._v_flat)
        else:
            for _ in range(steps):
                self._advance_numpy()

    def _advance_numpy(self):
        u, v = self.u, self.v
        lu = self.u.ravel()[self.nb].sum(axis=-1).reshape(self.n, self.n) - 4.0 * u
        lv = self.v.ravel()[self.nb].sum(axis=-1).reshape(self.n, self.n) - 4.0 * v
        r = u * v * v
        du = self.dt * (self.Du / self.dx ** 2 * lu - r + self.f * (1.0 - u))
        dv = self.dt * (self.Dv / self.dx ** 2 * lv + r - (self.f + self.k) * v)
        # In-place update: the C kernel holds persistent views into self.u/self.v
        # (self._u_flat/self._v_flat).  Re-binding them to a new array would leave
        # those views pointing at the old buffer, so the two back ends would
        # silently stop agreeing.  np.add(..., out=...) keeps one buffer forever.
        np.add(u, du, out=self.u)
        np.add(v, dv, out=self.v)
        self._u_flat = self.u.reshape(-1)
        self._v_flat = self.v.reshape(-1)
        self._reimpose()

    def _advance_hetero(self, pf: dict):
        u, v = self.u, self.v
        lu = self.u.ravel()[self.nb].sum(axis=-1).reshape(self.n, self.n) - 4.0 * u
        lv = self.v.ravel()[self.nb].sum(axis=-1).reshape(self.n, self.n) - 4.0 * v
        r = u * v * v
        f = pf.get("f", self.f)
        k = pf.get("k", self.k)
        Du = pf.get("Du", self.Du)
        Dv = pf.get("Dv", self.Dv)
        np.add(u, self.dt * (Du / self.dx ** 2 * lu - r + f * (1.0 - u)), out=self.u)
        np.add(v, self.dt * (Dv / self.dx ** 2 * lv + r - (f + k) * v), out=self.v)
        self._u_flat = self.u.reshape(-1)
        self._v_flat = self.v.reshape(-1)
        self._reimpose()

    def _reimpose(self):
        self.u[self.active == 0] = 1.0
        self.v[self.active == 0] = 0.0
        if self.bc == "reservoir":
            self._pin_frame()
        if self.fixed.any():
            fx = self.fixed.reshape(self.n, self.n) == 1
            self.u[fx] = 1.0
            self.v[fx] = 0.0

    # -- observation -----------------------------------------------------
    def metrics(self) -> dict[str, float]:
        v = self.v
        act = self.active == 1
        vv = v[act]
        out = {
            "time": self.t, "mass": float(vv.sum()) * self.dx * self.dx,
            "max_v": float(vv.max()) if vv.size else 0.0,
            "mean_v": float(vv.mean()) if vv.size else 0.0,
            "std_v": float(vv.std()) if vv.size else 0.0,
        }
        thr = 0.05
        out["active_area"] = float((vv > thr).sum()) * self.dx * self.dx
        out["threshold"] = thr
        return out

    def finish(self) -> RunResult:
        return RunResult(self.u.copy(), self.v.copy(),
                         np.asarray(self.trace["time"]), 
                         np.asarray(self.frames) if self.frames else np.empty((0,)),
                         {kk: np.asarray(vv) for kk, vv in self.trace.items()},
                         {"anomalies": list(self.anomalies), "wall_seconds": self.wall,
                          "backend": backend(), "core_hash": CORE_HASH})


# --------------------------------------------------------------------------
# one-shot helper
# --------------------------------------------------------------------------
def run(n=96, seed=7, f=0.035, k=0.065, steps=10000, dt=1.0, dx=1.0,
        Du=0.16, Dv=0.08, bc="periodic", mask=None, u=None, v=None,
        init_kw=None, keep_frames=False, every=100, param_field=None):
    """Convenience: build a Solver, run `steps` iterations, return (solver, result)."""
    if u is None or v is None:
        u, v = initial_state(n, seed, **(init_kw or {}))
    s = Solver(n=n, dx=dx, dt=dt, Du=Du, Dv=Dv, f=f, k=k, bc=bc, mask=mask,
               u=u, v=v, seed=seed, keep_frames=keep_frames,
               sample_interval=every, param_field=param_field)
    ok = s.step(steps)
    if not ok:
        s.anomalies.append("run stopped early by health check")
    return s, s.finish()


# --------------------------------------------------------------------------
# masks
# --------------------------------------------------------------------------
def wall_mask(n: int, cols: tuple[int, int] | None = None,
              rows: tuple[int, int] | None = None) -> np.ndarray:
    m = np.ones((n, n), np.uint8)
    if cols is not None:
        m[:, cols[0]:cols[1]] = 0
    if rows is not None:
        m[rows[0]:rows[1], :] = 0
    return m


def open_hole(mask: np.ndarray, rows: tuple[int, int], cols: tuple[int, int]) -> np.ndarray:
    m = mask.copy()
    m[rows[0]:rows[1], cols[0]:cols[1]] = 1
    return m


def pixel_mask(n: int, kind: str, **kw) -> np.ndarray:
    """ring / rect obstacle / channel geometry."""
    m = np.ones((n, n), np.uint8)
    yy, xx = np.indices((n, n))
    if kind == "ring":
        r0, r1, cy, cx = kw["r0"], kw["r1"], kw.get("cy", n // 2), kw.get("cx", n // 2)
        d2 = (yy - cy) ** 2 + (xx - cx) ** 2
        m[(d2 >= r0 * r0) & (d2 <= r1 * r1)] = 0
    elif kind == "rect":
        m[kw["r0"]:kw["r1"], kw["c0"]:kw["c1"]] = 0
    elif kind == "channel_walls":
        c0, c1 = kw["c0"], kw["c1"]
        m[:, c0:c1] = 0
        m[kw["gap0"]:kw["gap1"], c0:c1] = 1
    elif kind == "from_npz":
        # Caller-supplied boolean mask (1 = active, 0 = wall).  Work package L
        # needed this to compare a no-flux wall frame against a Dirichlet
        # reservoir frame; without it the attribution of the reservoir effect
        # could not be closed.
        z = np.load(kw["path"])
        m = z[kw.get("key", "active")].astype(np.uint8)
        if m.shape != (n, n):
            raise ValueError(f"mask {kw['path']} has shape {m.shape}, expected {(n, n)}")
    else:
        raise ValueError(kind)
    return m


# --------------------------------------------------------------------------
# integrity check
# --------------------------------------------------------------------------
def mass_balance_residual(solver: Solver, n_steps: int = 1) -> dict:
    """Check (M_new - M_old)/dt = sum(uv^2) - (f+k) sum(v) on the active set."""
    v0 = solver.v.copy()
    u0 = solver.u.copy()
    solver._advance(n_steps)
    dt = solver.dt
    act = solver.active == 1
    m0 = v0[act].sum() * solver.dx ** 2
    m1 = solver.v[act].sum() * solver.dx ** 2
    # trapezoidal reaction bookkeeping over the step
    r = (u0 * v0 * v0)[act].sum()
    sink = ((solver.f + solver.k) * v0)[act].sum()
    lhs = (m1 - m0) / (n_steps * dt)
    rhs = r - sink
    return {"lhs": float(lhs), "rhs": float(rhs), "abs_error": float(abs(lhs - rhs)),
            "rel_error": float(abs(lhs - rhs) / max(abs(rhs), 1e-30))}
