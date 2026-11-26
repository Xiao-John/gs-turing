/-
  GSTheoremLib.lean — Root Entry Point for the Gray–Scott / EGS Mini Theorem Library

  Pure Lean 4.36.0 (`Init` + native `Rat`), zero Mathlib, zero external dependencies,
  zero `sorry`, zero `native_decide`, zero custom axioms.

  Importing `GSTheoremLib` builds and verifies all shared core modules and all confirmed
  theorem suites:
    - `GSTheoremLib.Core.{QPair, Nagumo, Enclosure}`
    - `GSTheoremLib.Theorems.PlanarCrossover`
    - `GSTheoremLib.Theorems.M23Supersolution`
    - `GSTheoremLib.Theorems.M41ScalarReset`
    - `GSTheoremLib.Theorems.M44.{ContinuumPinning, CertCheck, CertW15..W18, SoundBridge, EndToEnd}`
-/

import GSTheoremLib.Core.QPair
import GSTheoremLib.Core.Nagumo
import GSTheoremLib.Core.Enclosure
import GSTheoremLib.Theorems.PlanarCrossover
import GSTheoremLib.Theorems.M23Supersolution
import GSTheoremLib.Theorems.M27SymmetryContraction
import GSTheoremLib.Theorems.M41ScalarReset
import GSTheoremLib.Theorems.M44.EndToEnd
