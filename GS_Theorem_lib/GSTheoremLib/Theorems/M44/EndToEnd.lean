/-
  M44EndToEnd.lean — End-to-End Formal Instantiation of M-44 Continuum Pinning
  for All Four Frozen Widths (w = 15, 16, 17, 18; 2,269 segments total)

  Combines:
    1. Pure-integer kernel verification (`M44CertW15` .. `M44CertW18`, `decide`),
    2. Exact `Rat` soundness bridge (`M44SoundBridge.checkFullRawCert_sound`),
    3. Exact `M44ContinuumPinning` analytical lemmas (Nagumo SOS, zero-calculus peak UB,
       Machin `π` enclosure, mouth bound `s(0,0) > -0.42`, global spline monotonicity).

  Zero Mathlib, zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import GSTheoremLib.Theorems.M44.SoundBridge
import GSTheoremLib.Theorems.M44.CertW15
import GSTheoremLib.Theorems.M44.CertW16
import GSTheoremLib.Theorems.M44.CertW17
import GSTheoremLib.Theorems.M44.CertW18

namespace M44ContinuumPinning

/-- Exact `Rat` spline certificate lifted from frozen `continuum_cert_w15.json` (569 segments). -/
def certW15Spline : SplineCert :=
  ⟨15, QPair.toRat (28125, 20449), certW15Segs.map RawSeg.toSpline⟩

/-- Exact `Rat` spline certificate lifted from frozen `continuum_cert_w16.json` (568 segments). -/
def certW16Spline : SplineCert :=
  ⟨16, QPair.toRat (32000, 20449), certW16Segs.map RawSeg.toSpline⟩

/-- Exact `Rat` spline certificate lifted from frozen `continuum_cert_w17.json` (566 segments). -/
def certW17Spline : SplineCert :=
  ⟨17, QPair.toRat (36125, 20449), certW17Segs.map RawSeg.toSpline⟩

/-- Exact `Rat` spline certificate lifted from frozen `continuum_cert_w18.json` (566 segments). -/
def certW18Spline : SplineCert :=
  ⟨18, QPair.toRat (40500, 20449), certW18Segs.map RawSeg.toSpline⟩

/-- **End-to-End Theorem (`w = 15`, 569 segments, `VERDICT.md` §三)**:
    For ANY `E : Int → Rat` satisfying `Exp50Spec E` (enclosing `exp(k/50)` at each 1/50 step),
    the exact spline `certW15Spline` satisfies:
    - exact domain radius `R0^2 = 500 * 15^2 / 286^2`,
    - left/right boundary joins (`s0 = -7/2`, `W = 1`, `W' < 0`; `0 < W_M < 3/10`, `W' = 0`, `f(W_M) < 0`),
    - global monotonicity `∀ sa ≤ sb, W(sb) ≤ W(sa)`,
    - strict pinning on the entire half-plane `s ≥ -42/100`: `W(s) ≤ 563362/1000000 < 3/5`,
    - strict neck bound on `s ≥ 0`: `W(s) ≤ 469624/1000000`,
    - pointwise PDE supersolution `W'' + J · f(W) < 0` on ALL 569 segments. -/
theorem m44_w15_end_to_end {E : Int → Rat} (hE : Exp50Spec E) :
    certW15Spline.R0sq = (500 * ((15 * 15 : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∃ first last,
      certW15Spline.segs.head? = some first ∧
      certW15Spline.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) ∧
    (∀ {sa sb : Rat}, sa ≤ sb → certW15Spline.evalSpline sb ≤ certW15Spline.evalSpline sa) ∧
    (∀ {s : Rat}, (-42 / 100 : Rat) ≤ s →
      certW15Spline.evalSpline s ≤ (563362 : Rat) / 1000000 ∧ certW15Spline.evalSpline s < 3 / 5) ∧
    (∀ {s : Rat}, (0 : Rat) ≤ s →
      certW15Spline.evalSpline s ≤ (469624 : Rat) / 1000000) ∧
    (∀ sp ∈ certW15Spline.segs,
      ∃ k : Int,
        sp.s0 = (k : Rat) / 100 ∧
        sp.s0 < sp.s1 ∧
        ∀ {s J : Rat},
          sp.s0 ≤ s → s ≤ sp.s1 →
          (0 : Rat) ≤ J →
          ((0 : Rat) < sp.s0 → certC2Lo certW15Spline.R0sq * (E k - 1) ≤ J) →
          (J ≤ certC2Hi certW15Spline.R0sq * (E (k + 1) + 1)) →
          (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  have h := checkFullRawCert_sound (by omega) (by omega) certW15_all_569_segments_verified hE
  rcases h with ⟨hR, hB, hMono, hM, hZ, hSup⟩
  refine ⟨hR, hB, hMono, ?_, ?_, hSup⟩
  · intro s hs
    have h1 : certW15Spline.evalSpline s ≤ (563362 : Rat) / 1000000 := hM hs
    exact ⟨h1, by grind⟩
  · intro s hs
    exact hZ hs

/-- **End-to-End Theorem (`w = 16`, 568 segments, `VERDICT.md` §三)**:
    Strict pinning on the entire half-plane `s ≥ -42/100`: `W(s) ≤ 582526/1000000 < 3/5`,
    neck bound on `s ≥ 0`: `W(s) ≤ 486358/1000000`, and pointwise PDE supersolution on ALL 568 segments. -/
theorem m44_w16_end_to_end {E : Int → Rat} (hE : Exp50Spec E) :
    certW16Spline.R0sq = (500 * ((16 * 16 : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∃ first last,
      certW16Spline.segs.head? = some first ∧
      certW16Spline.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) ∧
    (∀ {sa sb : Rat}, sa ≤ sb → certW16Spline.evalSpline sb ≤ certW16Spline.evalSpline sa) ∧
    (∀ {s : Rat}, (-42 / 100 : Rat) ≤ s →
      certW16Spline.evalSpline s ≤ (582526 : Rat) / 1000000 ∧ certW16Spline.evalSpline s < 3 / 5) ∧
    (∀ {s : Rat}, (0 : Rat) ≤ s →
      certW16Spline.evalSpline s ≤ (486358 : Rat) / 1000000) ∧
    (∀ sp ∈ certW16Spline.segs,
      ∃ k : Int,
        sp.s0 = (k : Rat) / 100 ∧
        sp.s0 < sp.s1 ∧
        ∀ {s J : Rat},
          sp.s0 ≤ s → s ≤ sp.s1 →
          (0 : Rat) ≤ J →
          ((0 : Rat) < sp.s0 → certC2Lo certW16Spline.R0sq * (E k - 1) ≤ J) →
          (J ≤ certC2Hi certW16Spline.R0sq * (E (k + 1) + 1)) →
          (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  have h := checkFullRawCert_sound (by omega) (by omega) certW16_all_568_segments_verified hE
  rcases h with ⟨hR, hB, hMono, hM, hZ, hSup⟩
  refine ⟨hR, hB, hMono, ?_, ?_, hSup⟩
  · intro s hs
    have h1 : certW16Spline.evalSpline s ≤ (582526 : Rat) / 1000000 := hM hs
    exact ⟨h1, by grind⟩
  · intro s hs
    exact hZ hs

/-- **End-to-End Theorem (`w = 17`, 566 segments, `VERDICT.md` §三)**:
    Mouth bound on `s ≥ -42/100`: `W(s) ≤ 611647/1000000`,
    strict pinning on `s ≥ 0`: `W(s) ≤ 514124/1000000 < 3/5`,
    and pointwise PDE supersolution on ALL 566 segments. -/
theorem m44_w17_end_to_end {E : Int → Rat} (hE : Exp50Spec E) :
    certW17Spline.R0sq = (500 * ((17 * 17 : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∃ first last,
      certW17Spline.segs.head? = some first ∧
      certW17Spline.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) ∧
    (∀ {sa sb : Rat}, sa ≤ sb → certW17Spline.evalSpline sb ≤ certW17Spline.evalSpline sa) ∧
    (∀ {s : Rat}, (-42 / 100 : Rat) ≤ s →
      certW17Spline.evalSpline s ≤ (611647 : Rat) / 1000000) ∧
    (∀ {s : Rat}, (0 : Rat) ≤ s →
      certW17Spline.evalSpline s ≤ (514124 : Rat) / 1000000 ∧ certW17Spline.evalSpline s < 3 / 5) ∧
    (∀ sp ∈ certW17Spline.segs,
      ∃ k : Int,
        sp.s0 = (k : Rat) / 100 ∧
        sp.s0 < sp.s1 ∧
        ∀ {s J : Rat},
          sp.s0 ≤ s → s ≤ sp.s1 →
          (0 : Rat) ≤ J →
          ((0 : Rat) < sp.s0 → certC2Lo certW17Spline.R0sq * (E k - 1) ≤ J) →
          (J ≤ certC2Hi certW17Spline.R0sq * (E (k + 1) + 1)) →
          (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  have h := checkFullRawCert_sound (by omega) (by omega) certW17_all_566_segments_verified hE
  rcases h with ⟨hR, hB, hMono, hM, hZ, hSup⟩
  refine ⟨hR, hB, hMono, ?_, ?_, hSup⟩
  · intro s hs
    exact hM hs
  · intro s hs
    have h1 : certW17Spline.evalSpline s ≤ (514124 : Rat) / 1000000 := hZ hs
    exact ⟨h1, by grind⟩

/-- **End-to-End Theorem (`w = 18`, 566 segments, `VERDICT.md` §三)**:
    Mouth bound on `s ≥ -42/100`: `W(s) ≤ 653688/1000000`,
    strict pinning on `s ≥ 0`: `W(s) ≤ 556889/1000000 < 3/5`,
    and pointwise PDE supersolution on ALL 566 segments. -/
theorem m44_w18_end_to_end {E : Int → Rat} (hE : Exp50Spec E) :
    certW18Spline.R0sq = (500 * ((18 * 18 : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∃ first last,
      certW18Spline.segs.head? = some first ∧
      certW18Spline.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) ∧
    (∀ {sa sb : Rat}, sa ≤ sb → certW18Spline.evalSpline sb ≤ certW18Spline.evalSpline sa) ∧
    (∀ {s : Rat}, (-42 / 100 : Rat) ≤ s →
      certW18Spline.evalSpline s ≤ (653688 : Rat) / 1000000) ∧
    (∀ {s : Rat}, (0 : Rat) ≤ s →
      certW18Spline.evalSpline s ≤ (556889 : Rat) / 1000000 ∧ certW18Spline.evalSpline s < 3 / 5) ∧
    (∀ sp ∈ certW18Spline.segs,
      ∃ k : Int,
        sp.s0 = (k : Rat) / 100 ∧
        sp.s0 < sp.s1 ∧
        ∀ {s J : Rat},
          sp.s0 ≤ s → s ≤ sp.s1 →
          (0 : Rat) ≤ J →
          ((0 : Rat) < sp.s0 → certC2Lo certW18Spline.R0sq * (E k - 1) ≤ J) →
          (J ≤ certC2Hi certW18Spline.R0sq * (E (k + 1) + 1)) →
          (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  have h := checkFullRawCert_sound (by omega) (by omega) certW18_all_566_segments_verified hE
  rcases h with ⟨hR, hB, hMono, hM, hZ, hSup⟩
  refine ⟨hR, hB, hMono, ?_, ?_, hSup⟩
  · intro s hs
    exact hM hs
  · intro s hs
    have h1 : certW18Spline.evalSpline s ≤ (556889 : Rat) / 1000000 := hZ hs
    exact ⟨h1, by grind⟩

end M44ContinuumPinning
