"""Generic numerical tools for analysing Gray-Scott states.

These modules exist because a computation-embedding study needs more than a time
integrator:

``rk4``        higher-order time integration on the fixed spatial grid, so a
               result can be attributed to the continuous-time system rather
               than to the explicit-Euler time map
``krylov``     matrix-free GMRES and Arnoldi (the Gray-Scott Jacobian is
               non-symmetric, so conjugate gradients is the wrong tool)
``newton``     matrix-free Newton for the stationary problem F(X) = 0, which is
               how a candidate configuration is pinned down exactly
``spectrum``   leading eigenpairs of the Jacobian at a state, i.e. whether that
               state is stable and along which direction it escapes
``jacobian``   sparse assembly of the Gray-Scott Jacobian, for the small problems
               where a sparse factorisation beats a matrix-free iteration
``fielddist``  translation-invariant distance between two fields, so "is this the
               same state?" can be asked without the answer depending on where the
               structure happens to sit

Modules are deliberately independent: importing ``numerics`` does not import
scipy, and each module runs its own self-test under ``python -m numerics.<name>``.
"""
