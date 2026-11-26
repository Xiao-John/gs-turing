/-
  Kernel-Checked Verifier (`M44CertCheck`) for the Four Frozen M-44 Spline JSON Certificates
  (2,269 total segments across w = 15, 16, 17, 18).
  Zero external dependencies (pure Lean 4.36.0 `Init`), zero `sorry`, zero `native_decide`.
-/
import GSTheoremLib.Theorems.M44.ContinuumPinning

namespace M44ContinuumPinning

/-! ## Part A: Outward-Rounded 12-Decimal `exp(k / 50)` Grid Enclosure & Soundness -/

def exp50Scale : Nat := 1000000000000
def e50LoN  : Nat := 1020201340026
def e50HiN  : Nat := 1020201340027
def en50LoN : Nat := 980198673306
def en50HiN : Nat := 980198673307

/-- Kernel-verified 12-decimal outward enclosure of `exp(±1/50)` from `expQ 7`. -/
theorem e50_step_enclosure :
    let (pLo, pHi) := expQ 7 ⟨1, 50, Nat.succ_pos 49⟩
    let (nLo, nHi) := expQ 7 ⟨-1, 50, Nat.succ_pos 49⟩
    Q.le ⟨(e50LoN : Int), exp50Scale, Nat.succ_pos _⟩ pLo = true ∧
    Q.le pHi ⟨(e50HiN : Int), exp50Scale, Nat.succ_pos _⟩ = true ∧
    Q.le ⟨(en50LoN : Int), exp50Scale, Nat.succ_pos _⟩ nLo = true ∧
    Q.le nHi ⟨(en50HiN : Int), exp50Scale, Nat.succ_pos _⟩ = true := by
  decide

/-- Outward-rounded multiplication step on scale `10^12`:
    floor `(a * b) / S` for lower bounds, ceil `(a * b + S - 1) / S` for upper bounds. -/
def stepLoN (stepN : Nat) : Nat → Nat
  | 0 => exp50Scale
  | k + 1 => (stepLoN stepN k * stepN) / exp50Scale

def stepHiN (stepN : Nat) : Nat → Nat
  | 0 => exp50Scale
  | k + 1 => (stepHiN stepN k * stepN + (exp50Scale - 1)) / exp50Scale

/-- Build `[(lo_0, hi_0), (lo_1, hi_1), ..., (lo_n, hi_n)]` by structural recursion. -/
def buildStepPairsRev (stepLo stepHi : Nat) : Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, acc => acc
  | n + 1, curLo, curHi, acc =>
    let nxtLo := (curLo * stepLo) / exp50Scale
    let nxtHi := (curHi * stepHi + (exp50Scale - 1)) / exp50Scale
    buildStepPairsRev stepLo stepHi n nxtLo nxtHi ((nxtLo, nxtHi) :: acc)

/-- Full outward-rounded `exp(k / 50)` list for `k = -350, -349, ..., 0, 1, ..., 250`. -/
def expGridList : List (Nat × Nat) :=
  let negPart := buildStepPairsRev en50LoN en50HiN 350 exp50Scale exp50Scale [(exp50Scale, exp50Scale)]
  let posPartRev := buildStepPairsRev e50LoN e50HiN 250 exp50Scale exp50Scale []
  negPart ++ posPartRev.reverse

/-- Soundness of outward-rounded `stepLoN` / `stepHiN` recurrence:
    For any `E : Nat → Rat` with `E 0 = 1`, `E (k+1) = E k * r`, and `stepLo/S ≤ r ≤ stepHi/S`
    (with `0 ≤ r`), every entry satisfies `stepLoN / S ≤ E k ≤ stepHiN / S`. -/
theorem stepLoHi_sound (E : Nat → Rat) (r : Rat) (stepLo stepHi : Nat)
    (hE0 : E 0 = 1) (hEstep : ∀ k, E (k + 1) = E k * r)
    (hr0 : (0 : Rat) ≤ r)
    (hlo : ((stepLo : Nat) : Rat) / (exp50Scale : Rat) ≤ r)
    (hhi : r ≤ ((stepHi : Nat) : Rat) / (exp50Scale : Rat)) :
    ∀ k : Nat,
      ((stepLoN stepLo k : Nat) : Rat) / (exp50Scale : Rat) ≤ E k ∧
      E k ≤ ((stepHiN stepHi k : Nat) : Rat) / (exp50Scale : Rat) := by
  have hnat_nn : ∀ n : Nat, (0 : Rat) ≤ (n : Rat) := by
    intro n; induction n with
    | zero => grind
    | succ n ih =>
      have h1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
      grind
  have hnat_le : ∀ {x y : Nat}, x ≤ y → (x : Rat) ≤ (y : Rat) := by
    intro x y hxy
    have hdiff : x + (y - x) = y := by omega
    have hd_nn := hnat_nn (y - x)
    have hc : ((x + (y - x) : Nat) : Rat) = (x : Rat) + ((y - x : Nat) : Rat) := by clear hEstep; grind
    rw [← hdiff, hc]
    clear hEstep; grind
  have hdiv_le : ∀ a : Nat, ((a / exp50Scale : Nat) : Rat) ≤ (a : Rat) / (exp50Scale : Rat) := by
    intro a
    have hmul_nat : (a / exp50Scale) * exp50Scale ≤ a := Nat.div_mul_le_self a exp50Scale
    have hmul_rat : ((a / exp50Scale : Nat) : Rat) * (exp50Scale : Rat) ≤ (a : Rat) := by
      have hcast : (((a / exp50Scale) * exp50Scale : Nat) : Rat) =
          ((a / exp50Scale : Nat) : Rat) * (exp50Scale : Rat) := by clear hEstep; grind
      rw [← hcast]; exact hnat_le hmul_nat
    have hdiv := Rat.mul_le_mul_of_nonneg_left hmul_rat (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
    unfold exp50Scale at hdiv ⊢
    clear hEstep; grind
  have hceil_ge : ∀ a : Nat, (a : Rat) / (exp50Scale : Rat) ≤ (((a + (exp50Scale - 1)) / exp50Scale : Nat) : Rat) := by
    intro a
    have hmul_nat : a ≤ ((a + (exp50Scale - 1)) / exp50Scale) * exp50Scale := by
      have hS : 0 < exp50Scale := by unfold exp50Scale; omega
      have hmod := Nat.div_add_mod (a + (exp50Scale - 1)) exp50Scale
      have hlt := Nat.mod_lt (a + (exp50Scale - 1)) hS
      unfold exp50Scale at hmod hlt ⊢
      omega
    have hmul_rat : (a : Rat) ≤ (((a + (exp50Scale - 1)) / exp50Scale : Nat) : Rat) * (exp50Scale : Rat) := by
      have hcast : ((((a + (exp50Scale - 1)) / exp50Scale) * exp50Scale : Nat) : Rat) =
          (((a + (exp50Scale - 1)) / exp50Scale : Nat) : Rat) * (exp50Scale : Rat) := by clear hEstep; grind
      rw [← hcast]; exact hnat_le hmul_nat
    have hdiv := Rat.mul_le_mul_of_nonneg_left hmul_rat (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
    unfold exp50Scale at hdiv ⊢
    clear hEstep; grind
  intro k
  induction k with
  | zero =>
    simp only [stepLoN, stepHiN, hE0]
    unfold exp50Scale; grind
  | succ k ih =>
    rw [hEstep k]
    simp only [stepLoN, stepHiN]
    have hEk0 : (0 : Rat) ≤ E k := by
      have hnn := hnat_nn (stepLoN stepLo k)
      have hdiv0 : (0 : Rat) ≤ ((stepLoN stepLo k : Nat) : Rat) / (exp50Scale : Rat) := by
        have := Rat.mul_nonneg hnn (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
        unfold exp50Scale at this ⊢; grind
      grind
    constructor
    · have h1 := hdiv_le (stepLoN stepLo k * stepLo)
      have h1s := Rat.mul_le_mul_of_nonneg_left h1 (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
      have hcast : ((stepLoN stepLo k * stepLo : Nat) : Rat) =
          ((stepLoN stepLo k : Nat) : Rat) * ((stepLo : Nat) : Rat) := by grind
      have h2 := Rat.mul_le_mul_of_nonneg_left hlo (by
        have hnn := hnat_nn (stepLoN stepLo k)
        have := Rat.mul_nonneg hnn (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
        unfold exp50Scale at this ⊢; grind : (0 : Rat) ≤ ((stepLoN stepLo k : Nat) : Rat) / (exp50Scale : Rat))
      have h3 := Rat.mul_le_mul_of_nonneg_left ih.1 hr0
      unfold exp50Scale at h1s h2 h3 ⊢
      grind
    · have h1 := hceil_ge (stepHiN stepHi k * stepHi)
      have h1s := Rat.mul_le_mul_of_nonneg_left h1 (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
      have hcast : ((stepHiN stepHi k * stepHi : Nat) : Rat) =
          ((stepHiN stepHi k : Nat) : Rat) * ((stepHi : Nat) : Rat) := by grind
      have h2 := Rat.mul_le_mul_of_nonneg_left hhi hEk0
      have h3 := Rat.mul_le_mul_of_nonneg_left ih.2 (by
        have hnn := hnat_nn stepHi
        have := Rat.mul_nonneg hnn (by unfold exp50Scale; grind : (0 : Rat) ≤ (1 : Rat) / (exp50Scale : Rat))
        unfold exp50Scale at this ⊢; grind : (0 : Rat) ≤ ((stepHi : Nat) : Rat) / (exp50Scale : Rat))
      unfold exp50Scale at h1s h2 h3 ⊢
      grind


/-! ## Part B: Pure Structural-Recursion Kernel Checker for Frozen JSON Certificates -/

/-- Exact rational pair `(num, den)` directly matching JSON `[num, den]`. -/
abbrev QPair := Int × Nat

@[inline] def qpEq (a b : QPair) : Bool :=
  a.1 * (b.2 : Int) == b.1 * (a.2 : Int)

@[inline] def qpLe (a b : QPair) : Bool :=
  decide (a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int))

@[inline] def qpLt (a b : QPair) : Bool :=
  decide (a.1 * (b.2 : Int) < b.1 * (a.2 : Int))

@[inline] def qpAdd (a b : QPair) : QPair :=
  (a.1 * (b.2 : Int) + b.1 * (a.2 : Int), a.2 * b.2)

@[inline] def qpSub (a b : QPair) : QPair :=
  (a.1 * (b.2 : Int) - b.1 * (a.2 : Int), a.2 * b.2)

@[inline] def qpMul (a b : QPair) : QPair :=
  (a.1 * b.1, a.2 * b.2)

@[inline] def qpMax (a b : QPair) : QPair :=
  if qpLe a b then b else a

@[inline] def qpNagumoF (w : QPair) : QPair :=
  let n := w.1
  let d : Int := (w.2 : Int)
  let num := n * (d - n) * (10 * n - 3 * d)
  let den := 10 * w.2 * w.2 * w.2
  (num, den)

/-- Exact `fPeakUB = f(729/1000) + f'(729/1000) * (1/1000) = 84753888 / 1000000000` (exact!). -/
def fPeakUBPair : QPair := (84753888, 1000000000)

theorem fPeakUBPair_exact :
    (fPeakUBPair.1 : Rat) / (fPeakUBPair.2 : Rat) = fPeakUB := by
  unfold fPeakUBPair fPeakUB nagumoF nagumoF' wPeakLo wPeakHi
  grind

@[inline] def qpFMaxUB (a b : QPair) : QPair :=
  let m := qpMax (qpNagumoF a) (qpNagumoF b)
  if qpLt (729, 1000) b && qpLt a (730, 1000) then qpMax m fPeakUBPair else m

/-- Raw segment directly matching one interval of `continuum_cert_w*.json`. -/
structure RawSeg where
  s0  : QPair
  s1  : QPair
  w0  : QPair
  w1  : QPair
  wp0 : QPair
  wp1 : QPair
  c   : QPair

/-- Compact `c2Lo`, `c2Hi` rational pairs from `R0sq = (rNum, rDen)` and `piLo/piHi`. -/
def rawC2Lo (r0sq : QPair) : QPair :=
  (4 * r0sq.1 * 10000000000000000, r0sq.2 * (314159266 * 314159266))

def rawC2Hi (r0sq : QPair) : QPair :=
  (4 * r0sq.1 * 10000000000000000, r0sq.2 * (314159265 * 314159265))

/-- Check one segment given `k` (so `s0 = k/100`), `e0 = exp(k/50)`, and `e1 = exp((k+1)/50)`. -/
def checkRawSegWithGrid (c2Lo c2Hi : QPair) (k : Int) (e0Lo : Nat) (e1Hi : Nat) (seg : RawSeg) : Bool :=
  if seg.s0.2 == 0 || seg.s1.2 == 0 || seg.w0.2 == 0 || seg.w1.2 == 0 ||
     seg.wp0.2 == 0 || seg.wp1.2 == 0 || seg.c.2 == 0 then false
  else
    let ds := qpSub seg.s1 seg.s0
    let rhsW1 := qpAdd (qpAdd seg.w0 (qpMul seg.wp0 ds))
                       (qpMul seg.c (ds.1 * ds.1, 2 * ds.2 * ds.2))
    let rhsWp1 := qpAdd seg.wp0 (qpMul seg.c ds)
    let geomOk :=
      decide (0 < ds.1) &&
      qpEq seg.s0 (k, 100) &&
      qpEq seg.w1 rhsW1 &&
      qpEq seg.wp1 rhsWp1 &&
      decide (seg.wp0.1 ≤ 0) &&
      decide (seg.wp1.1 ≤ 0) &&
      decide (0 ≤ seg.w1.1) &&
      qpLe seg.w0 (1, 1)
    if !geomOk then false
    else
      let fHi := qpFMaxUB seg.w1 seg.w0
      if decide (0 ≤ fHi.1) then
        if !qpEq seg.s1 (k + 1, 100) then false
        else
          let e2Hi : QPair := ((e1Hi : Int), exp50Scale)
          let term := qpMul (qpMul c2Hi (qpAdd e2Hi (1, 1))) fHi
          qpLt (qpAdd seg.c term) (0, 1)
      else
        let e2Lo : QPair := ((e0Lo : Int), exp50Scale)
        if !decide (0 < k) || !qpLt (1, 1) e2Lo then false
        else
          let term := qpMul (qpMul c2Lo (qpSub e2Lo (1, 1))) fHi
          qpLt (qpAdd seg.c term) (0, 1)

/-- Single-pass structural recursion over `List RawSeg` zipped with `expGridList`:
    checks EVERY segment's geometry, `C¹` chaining to next segment, supersolution residual,
    right-tail boundary on the last segment, and knot bounds at `s = -42/100` & `s = 0`. -/
def checkSegsLoop (c2Lo c2Hi uMouth uS0 : QPair) :
    Int → List (Nat × Nat) → List RawSeg → Bool → Bool → Bool
  | _, _, [], mouthOk, s0Ok => mouthOk && s0Ok
  | k, (e0Lo, _) :: (e1Lo, e1Hi) :: _gRest, [last], mouthOk, s0Ok =>
    let segOk := checkRawSegWithGrid c2Lo c2Hi k e0Lo e1Hi last
    let tailOk := decide (0 < last.w1.1) && qpLt last.w1 (3, 10) && (last.wp1.1 == 0)
    let mOk := mouthOk || (k == -42 && qpLe last.w0 uMouth)
    let zOk := s0Ok || (k == 0 && qpLe last.w0 uS0)
    segOk && tailOk && mOk && zOk && (e1Lo > 0)
  | k, (e0Lo, _) :: (e1Lo, e1Hi) :: gRest, seg :: nxt :: rest, mouthOk, s0Ok =>
    let segOk := checkRawSegWithGrid c2Lo c2Hi k e0Lo e1Hi seg
    let chainOk := qpEq seg.s1 nxt.s0 && qpEq seg.w1 nxt.w0 && qpEq seg.wp1 nxt.wp0
    if !(segOk && chainOk) then false
    else
      let mOk := mouthOk || (k == -42 && qpLe seg.w0 uMouth)
      let zOk := s0Ok || (k == 0 && qpLe seg.w0 uS0)
      checkSegsLoop c2Lo c2Hi uMouth uS0 (k + 1) ((e1Lo, e1Hi) :: gRest) (nxt :: rest) mOk zOk
  | _, _, _, _, _ => false

/-- Full pure-structural-recursion kernel verifier for a frozen M-44 JSON spline certificate. -/
def checkFullRawCert (wCells : Nat) (r0sq : QPair) (segs : List RawSeg)
    (uMouth uS0 : QPair) : Bool :=
  match segs with
  | [] => false
  | first :: _ =>
    let r0Ok := r0sq.2 != 0 && qpEq r0sq (500 * (wCells * wCells : Int), 286 * 286)
    let leftOk := qpEq first.s0 (-7, 2) && qpEq first.w0 (1, 1) && decide (first.wp0.1 < 0)
    if !(r0Ok && leftOk) then false
    else
      checkSegsLoop (rawC2Lo r0sq) (rawC2Hi r0sq) uMouth uS0 (-350) expGridList segs false false

end M44ContinuumPinning
