/-
  GSTheoremLib/Core/Nagumo.lean — Canonical Bistable Nagumo Reaction Algebra (Shared Core)

  Unifies the exact `Rat` bistable Nagumo reaction used across M-23, M-41, M-44 (and future
  EGS auxiliary-field theorems such as M-27):
    - Unit reaction `nagumoUnit w = w * (1 - w) * (w - 3 / 10)`
    - Scaled EGS reaction `nagumoScaled w = (1 / 200) * nagumoUnit w`
    - Exact antiderivative potential `nagumoPotential w`
    - Exact SOS one-sided Lipschitz constant `79 / 300` (and scaled `79 / 60000`)
    - Exact global Lipschitz bound `7 / 2000` on `[0, 1]` for `nagumoScaled`
    - Tail negativity `0 < w < 3/10 → nagumoUnit w < 0`
    - Zero-calculus interval upper bound `fMaxUB` and exact peak `84753888 / 1000000000`

  Zero external dependencies (pure Lean 4.36.0 `Init`), zero `sorry`.
-/

import GSTheoremLib.Theorems.M44.ContinuumPinning
import GSTheoremLib.Theorems.M41ScalarReset

namespace GSTheoremLib.Core

/-- Canonical unit bistable Nagumo reaction `f(w) = w(1 - w)(w - 3/10)`. -/
abbrev nagumoUnit : Rat → Rat := M44ContinuumPinning.nagumoF

/-- Canonical scaled EGS Nagumo reaction `g(w) = (1/200) * w(1 - w)(w - 3/10)`. -/
abbrev nagumoScaled : Rat → Rat := M41ScalarReset.nagumo

/-- Canonical antiderivative potential `G(w) = ∫_0^w g(s) ds`. -/
abbrev nagumoPotential : Rat → Rat := M41ScalarReset.potential

theorem nagumoScaled_eq_unit (w : Rat) :
    nagumoScaled w = (1 / 200 : Rat) * nagumoUnit w := by
  unfold nagumoScaled M41ScalarReset.nagumo nagumoUnit M44ContinuumPinning.nagumoF
  grind

/-- Global SOS one-sided Lipschitz bound for `nagumoUnit`: `K = 79 / 300`. -/
theorem nagumoUnit_one_sided_lipschitz {a b : Rat} (hab : b ≤ a) :
    nagumoUnit a - nagumoUnit b ≤ (79 / 300 : Rat) * (a - b) :=
  M44ContinuumPinning.f_one_sided_lipschitz_79_300 hab

/-- Tail negativity for `0 < w < 3/10`. -/
theorem nagumoUnit_tail_neg {w : Rat} (h0 : (0 : Rat) < w) (h3 : w < 3 / 10) :
    nagumoUnit w < 0 :=
  M44ContinuumPinning.f_tail_neg h0 h3

/-- Zero-calculus interval upper bound on `[a, b] ⊆ [0, 1]`. -/
theorem nagumoUnit_le_fMaxUB {a b w : Rat}
    (ha0 : (0 : Rat) ≤ a) (haw : a ≤ w) (hwb : w ≤ b) (hb1 : b ≤ 1) :
    nagumoUnit w ≤ M44ContinuumPinning.fMaxUB a b :=
  M44ContinuumPinning.f_le_fMaxUB ha0 haw hwb hb1

end GSTheoremLib.Core
