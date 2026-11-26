/* Gray-Scott 5-point explicit Euler kernel.
 * Shared numerical core: only the solver owner modifies this file.
 *
 * Model:
 *   du/dt = Du * lap(u) - u*v^2 + f*(1-u)
 *   dv/dt = Dv * lap(v) + u*v^2 - (f+k)*v
 *
 * Boundary handling for the neighbour gather (bc_mode):
 *   0 periodic : index wraps
 *   1 noflux   : outside neighbour is the cell itself (zero flux)
 *   2 reservoir: same neighbour rule as noflux; the caller resets the frame
 *                to (u=1, v=0) after every step (edge is overwritten, no ghost cells).
 *   3 dirichlet: same neighbour rule as noflux; the caller sets a mask of fixed
 *                cells to (u=1, v=0) after every step.  Recorded as a different
 *                boundary kind from reservoir because the fixed set may be internal.
 *
 * Walls are expressed with `active` (1 = reacting cell, 0 = impermeable wall).
 * A neighbour that lies in a wall is replaced by the cell itself, which gives a
 * zero diffusive flux across that edge.  Wall cells are pinned to u=1, v=0 by
 * the caller's re-imposition (they never react).
 *
 * u is updated from (u,v); v then uses the OLD u (a temporary copy is taken).
 */
#include <math.h>

typedef struct {
    long steps_done;
    long nan_hits;
    double max_abs_u;
    double max_abs_v;
} gs_report;

static void gs_step(double *restrict u, double *restrict v, double *restrict ut,
                    double *restrict vt, const int *restrict nb, const unsigned char *restrict act,
                    long ncells, double Du, double Dv, double f, double k, double dt)
{
    long i;
    for (i = 0; i < ncells; ++i) {
        const int *q = nb + 4 * i;
        double u0 = u[i];
        double v0 = v[i];
        double r = u0 * v0 * v0;
        double lu = u[q[0]] + u[q[1]] + u[q[2]] + u[q[3]] - 4.0 * u0;
        double lv = v[q[0]] + v[q[1]] + v[q[2]] + v[q[3]] - 4.0 * v0;
        ut[i] = u0 + dt * (Du * lu - r + f * (1.0 - u0));
        vt[i] = v0 + dt * (Dv * lv + r - (f + k) * v0);
    }
    (void)act;
    for (i = 0; i < ncells; ++i) {
        u[i] = ut[i];
        v[i] = vt[i];
    }
}

/* reservoir: pin the one-cell frame to fresh medium after each step */
static void gs_pin_frame(double *u, double *v, int n)
{
    int j;
    for (j = 0; j < n; ++j) {
        u[j] = 1.0;                 v[j] = 0.0;                 /* row 0 */
        u[(long)(n - 1) * n + j] = 1.0; v[(long)(n - 1) * n + j] = 0.0; /* row n-1 */
        u[(long)j * n] = 1.0;       v[(long)j * n] = 0.0;       /* col 0 */
        u[(long)j * n + (n - 1)] = 1.0; v[(long)j * n + (n - 1)] = 0.0; /* col n-1 */
    }
}

int gs_evolve(double *u, double *v, double *ut, double *vt,
              const int *nb, const unsigned char *active,
              int n, long steps, double Du, double Dv, double f, double k, double dt,
              int bc_mode, const unsigned char *fixed, double *uout, double *vout)
{
    long step, i;
    long ncells = (long)n * (long)n;
    gs_report rep;
    rep.steps_done = 0; rep.nan_hits = 0; rep.max_abs_u = 0.0; rep.max_abs_v = 0.0;

    for (step = 0; step < steps; ++step) {
        gs_step(u, v, ut, vt, nb, active, ncells, Du, Dv, f, k, dt);

        /* re-impose non-reacting cells after the update (never before) */
        if (active) {
            for (i = 0; i < ncells; ++i) {
                if (!active[i]) { u[i] = 1.0; v[i] = 0.0; }
            }
        }
        if (bc_mode == 2) {
            gs_pin_frame(u, v, n);
        } else if (bc_mode == 3 && fixed) {
            for (i = 0; i < ncells; ++i) {
                if (fixed[i]) { u[i] = 1.0; v[i] = 0.0; }
            }
        }
        rep.steps_done++;
    }

    /* copy out (u,v) into caller-owned arrays */
    for (i = 0; i < ncells; ++i) { uout[i] = u[i]; vout[i] = v[i]; }
    return 0;
}

/* Health probe over the current state. */
int gs_probe(const double *u, const double *v, int n, double *out)
{
    long i, ncells = (long)n * (long)n;
    double mu = 0.0, mv = 0.0;
    int bad = 0;
    for (i = 0; i < ncells; ++i) {
        double a = fabs(u[i]), b = fabs(v[i]);
        if (!isfinite(u[i]) || !isfinite(v[i])) bad = 1;
        if (a > mu) mu = a;
        if (b > mv) mv = b;
    }
    out[0] = mu; out[1] = mv; out[2] = (double)bad;
    return bad;
}

/* --------------------------------------------------------------------------
 * Rectangular periodic kernel (nx x ny, row-major, i = j*nx + k).
 *
 * Same 5-point Laplacian and synchronous explicit Euler as gs_step, but with a
 * scalar resource level:
 *     du/dt = Du*lap(u) - u*v^2 + f*(ures - u)
 *     dv/dt = Dv*lap(v) + u*v^2 - (f+k)*v
 * u_res == 1 reduces this to the plain model of gs_step.
 *
 * Per-timestep acceptance rule.  The candidate state is computed into scratch
 * (u and v are NOT touched), the WHOLE candidate is then scanned, and it is
 * copied into (u,v) only if every cell passed.  Two passes, deliberately:
 * fusing the scan into the copy would leave the fields half-advanced when a bad
 * value is found, so the state would be neither the last accepted one nor the
 * new one.  A rejected step therefore leaves (u,v) exactly at the last accepted
 * state -- nothing is advanced, nothing is clipped.
 *
 * The caller sees why a run stopped (kind + cell + the offending values), so an
 * early stop can never be recorded as "the pattern did not move".
 * -------------------------------------------------------------------------- */
typedef struct {
    long steps_done;     /* accepted steps in this call */
    long bad_step;       /* step index of the first rejected candidate, -1 if none */
    int  bad_kind;       /* 0 ok, 1 non-finite, 2 below -neg_tol, 3 above over_tol */
    long bad_index;      /* flat cell index of the first offending value */
    double bad_u;        /* offending u (or the non-finite value) */
    double bad_v;        /* offending v */
} gs_rect_report;

static void gs_rect_candidate(const double *restrict u, const double *restrict v,
                              double *restrict ut, double *restrict vt,
                              int nx, int ny, double Du, double Dv, double f,
                              double k, double dt, double ures, double inv_h2)
{
    int j, i;
    for (j = 0; j < ny; ++j) {
        const long rowo = (long)j * nx;
        const long rowm = (long)((j == 0) ? ny - 1 : j - 1) * nx;
        const long rowp = (long)((j == ny - 1) ? 0 : j + 1) * nx;
        for (i = 0; i < nx; ++i) {
            const int im = (i == 0) ? nx - 1 : i - 1;
            const int ip = (i == nx - 1) ? 0 : i + 1;
            const long c = rowo + i;
            const double u0 = u[c], v0 = v[c];
            const double r = u0 * v0 * v0;
            /* the raw 5-point stencil is scaled by 1/h^2 here: Du and Dv keep
             * their physical meaning and h is passed in explicitly, so a caller
             * cannot get a silent dx=1 assumption. */
            const double lu = inv_h2 * (u[rowm + i] + u[rowp + i]
                                        + u[rowo + ip] + u[rowo + im] - 4.0 * u0);
            const double lv = inv_h2 * (v[rowm + i] + v[rowp + i]
                                        + v[rowo + ip] + v[rowo + im] - 4.0 * v0);
            ut[c] = u0 + dt * (Du * lu - r + f * (ures - u0));
            vt[c] = v0 + dt * (Dv * lv + r - (f + k) * v0);
        }
    }
}

int gs_evolve_rect(double *u, double *v, double *ut, double *vt,
                   int nx, int ny, long steps,
                   double Du, double Dv, double f, double k, double dt, double ures,
                   double inv_h2, double neg_tol, double over_tol,
                   gs_rect_report *rep)
{
    long step, i;
    const long ncells = (long)nx * (long)ny;
    rep->steps_done = 0; rep->bad_step = -1; rep->bad_kind = 0;
    rep->bad_index = -1; rep->bad_u = 0.0; rep->bad_v = 0.0;

    for (step = 0; step < steps; ++step) {
        gs_rect_candidate(u, v, ut, vt, nx, ny, Du, Dv, f, k, dt, ures, inv_h2);
        for (i = 0; i < ncells; ++i) {
            const double a = ut[i], b = vt[i];
            int kind = 0;
            if (!isfinite(a) || !isfinite(b)) kind = 1;
            else if (a < -neg_tol || b < -neg_tol) kind = 2;
            else if (a > over_tol || b > over_tol) kind = 3;
            if (kind) {
                rep->bad_step = step; rep->bad_kind = kind;
                rep->bad_index = i; rep->bad_u = a; rep->bad_v = b;
                return kind;
            }
        }
        for (i = 0; i < ncells; ++i) { u[i] = ut[i]; v[i] = vt[i]; }
        rep->steps_done++;
    }
    return 0;
}
