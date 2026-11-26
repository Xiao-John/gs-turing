/-
  GSTheoremLib/Core/Enclosure.lean — Kernel-Verified Rational Enclosures (`π`, `exp(k/50)`)

  Re-exports the zero-dependency, kernel-verified rational enclosures used across
  continuum PDE and geometric bounds:
    - Machin `π` enclosure `3.14159265 < pi_machin < 3.14159266` (zero axioms!)
    - 12-decimal outward-rounded `exp(±1/50)` step enclosure (`e50_step_enclosure`)
    - `Exp50Spec` and 601-point grid enclosure `expGridList_encloses` for `k ∈ [-350, 250]`

  Zero external dependencies (pure Lean 4.36.0 `Init`), zero `sorry`, zero `native_decide`.
-/

import GSTheoremLib.Theorems.M44.SoundBridge

namespace GSTheoremLib.Core

/-- Kernel-verified Machin `π` enclosure (`3.14159265 < pi < 3.14159266`, zero axioms). -/
abbrev pi_machin_enclosure := @M44ContinuumPinning.pi_machin_enclosure

/-- Kernel-verified 12-decimal outward-rounded `exp(±1/50)` step bounds. -/
abbrev e50_step_enclosure := @M44ContinuumPinning.e50_step_enclosure

/-- Axiomatic specification for any `E : Int → Rat` enclosing `exp(k/50)` step-by-step. -/
abbrev Exp50Spec := M44ContinuumPinning.Exp50Spec

/-- Inductive soundness of the 601-point outward-rounded `exp(k/50)` grid on `k ∈ [-350, 250]`. -/
abbrev expGridList_encloses := @M44ContinuumPinning.expGridList_encloses

end GSTheoremLib.Core
