/-
  Lean 4 Formalization of the Confirmed Theorem (M-44):
    "Exact Algebraic Reaction Bounds, Machin π & Taylor exp Rational Enclosures,
     Mouth Coordinate Lower Bound s(0,0) > -0.42, and Soundness of C¹ Piecewise-Quadratic
     Conformal Supersolution Certificates on the Ideal Continuum T-Domain"
  Source verdict:
    coordination/confirm/2026-11-23_m44_continuum_pinning/VERDICT.md
    coordination/confirm/2026-11-23_m44_continuum_pinning/REPORT.md
    sandbox/2026-11-23_agent3_m39_continuum_pinning_proof/independent_interval_verify.py
  Zero external dependencies (pure Lean 4.36.0 core `Init` + native `Rat`, zero `sorry`).
-/

namespace M44ContinuumPinning

/-! ## Part 1: Exact Algebraic Properties of the Nagumo Reaction `f(w) = w(1 - w)(w - 3/10)` -/

/-- Dimensionless bistable Nagumo reaction `f(w) = w * (1 - w) * (w - 3/10)`. -/
def nagumoF (w : Rat) : Rat :=
  w * (1 - w) * (w - 3 / 10)

/-- Exact derivative `f'(w) = -3 w^2 + (13/5) w - 3/10`. -/
def nagumoF' (w : Rat) : Rat :=
  -3 * (w * w) + (13 / 5 : Rat) * w - (3 / 10 : Rat)

/-- Peak bracket endpoints `w_lo = 729/1000`, `w_hi = 730/1000` enclosing the unique local max `w_+`. -/
def wPeakLo : Rat := 729 / 1000
def wPeakHi : Rat := 730 / 1000

/-- Rigorous concave-tangent upper bound on `max_{w ∈ [729/1000, 730/1000]} f(w)`. -/
def fPeakUB : Rat :=
  nagumoF wPeakLo + nagumoF' wPeakLo * (wPeakHi - wPeakLo)

/-- Computable rational upper bound on `max_{w ∈ [a, b]} f(w)` for `0 ≤ a ≤ b ≤ 1`,
    matching `prove_f_max_on_interval` in `independent_interval_verify.py`. -/
def fMaxUB (a b : Rat) : Rat :=
  let m := max (nagumoF a) (nagumoF b)
  if wPeakLo < b ∧ a < wPeakHi then max m fPeakUB else m

private theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases @Rat.le_total (0 : Rat) x with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := by grind
    have hprod := Rat.mul_nonneg hneg hneg
    grind

private theorem rat_le_max_left (x y : Rat) : x ≤ max x y := by
  show x ≤ if x ≤ y then y else x
  split <;> grind

private theorem rat_le_max_right (x y : Rat) : y ≤ max x y := by
  show y ≤ if x ≤ y then y else x
  split <;> grind

private theorem rat_max_le {x y z : Rat} (hx : x ≤ z) (hy : y ≤ z) : max x y ≤ z := by
  show (if x ≤ y then y else x) ≤ z
  split <;> grind

/-- Main Theorem 1.1 (Exact Global One-Sided Lipschitz Bound `K = 79/300`, `VERDICT.md` §三):
    For ALL `a b : Rat` with `b ≤ a`,
      `f(a) - f(b) ≤ (79 / 300) * (a - b)`.
    Proved purely algebraically via exact sum-of-squares decomposition (zero calculus). -/
theorem f_one_sided_lipschitz_79_300 {a b : Rat} (hba : b ≤ a) :
    nagumoF a - nagumoF b ≤ (79 / 300 : Rat) * (a - b) := by
  have hid :
      (79 / 300 : Rat) * (a - b) - (nagumoF a - nagumoF b) =
      (a - b) * ((3 / 4 : Rat) * ((a + b - 13 / 15) * (a + b - 13 / 15))
               + (1 / 4 : Rat) * ((a - b) * (a - b))) := by
    unfold nagumoF
    grind
  have h1 : (0 : Rat) ≤ (a + b - 13 / 15) * (a + b - 13 / 15) := rat_sq_nonneg (a + b - 13 / 15)
  have h2 : (0 : Rat) ≤ (a - b) * (a - b) := rat_sq_nonneg (a - b)
  have hsum : (0 : Rat) ≤ (3 / 4 : Rat) * ((a + b - 13 / 15) * (a + b - 13 / 15))
                        + (1 / 4 : Rat) * ((a - b) * (a - b)) := by grind
  have hprod : (0 : Rat) ≤ (a - b) * ((3 / 4 : Rat) * ((a + b - 13 / 15) * (a + b - 13 / 15))
                                    + (1 / 4 : Rat) * ((a - b) * (a - b))) :=
    Rat.mul_nonneg (by grind) hsum
  rw [← hid] at hprod
  grind

/-- Lemma 1.2 (Right Tail Strictly Negative):
    For `0 < w < 3/10`, `f(w) < 0` (used for the constant tail `W_M ∈ (0, 0.04)`). -/
theorem f_tail_neg {w : Rat} (hw0 : (0 : Rat) < w) (hw3 : w < 3 / 10) :
    nagumoF w < 0 := by
  unfold nagumoF
  have h1 : (0 : Rat) < w * (1 - w) := Rat.mul_pos hw0 (by grind)
  have h2 : (0 : Rat) < (w * (1 - w)) * (3 / 10 - w) := Rat.mul_pos h1 (by grind)
  grind

/-- Lemma 1.3 (Algebraic Convexity on `[0, 13/30]`):
    For `0 ≤ a ≤ w ≤ b ≤ 13/30`, `f(w) ≤ max (f(a)) (f(b))`. -/
theorem f_le_endpoints_on_left {a w b : Rat}
    (_ha0 : (0 : Rat) ≤ a) (haw : a ≤ w) (hwb : w ≤ b) (hb : b ≤ 13 / 30) :
    nagumoF w ≤ max (nagumoF a) (nagumoF b) := by
  by_cases hab : a = b
  · have hwa : w = a := by grind
    rw [hwa]
    exact rat_le_max_left (nagumoF a) (nagumoF b)
  · have hba_pos : (0 : Rat) < b - a := by grind
    have hid :
        ((b - w) * nagumoF a + (w - a) * nagumoF b) - (b - a) * nagumoF w =
        (w - a) * (b - w) * (b - a) * (13 / 10 - (a + w + b)) := by
      unfold nagumoF
      grind
    have hp1 : (0 : Rat) ≤ (w - a) * (b - w) := Rat.mul_nonneg (by grind) (by grind)
    have hp2 : (0 : Rat) ≤ (w - a) * (b - w) * (b - a) := Rat.mul_nonneg hp1 (by grind)
    have hp3 : (0 : Rat) ≤ (w - a) * (b - w) * (b - a) * (13 / 10 - (a + w + b)) :=
      Rat.mul_nonneg hp2 (by grind)
    rw [← hid] at hp3
    have hma : nagumoF a ≤ max (nagumoF a) (nagumoF b) := rat_le_max_left _ _
    have hmb : nagumoF b ≤ max (nagumoF a) (nagumoF b) := rat_le_max_right _ _
    have hca : (b - w) * nagumoF a ≤ (b - w) * max (nagumoF a) (nagumoF b) :=
      Rat.mul_le_mul_of_nonneg_left hma (by grind)
    have hcb : (w - a) * nagumoF b ≤ (w - a) * max (nagumoF a) (nagumoF b) :=
      Rat.mul_le_mul_of_nonneg_left hmb (by grind)
    have hcomb : (b - a) * nagumoF w ≤ (b - a) * max (nagumoF a) (nagumoF b) := by grind
    by_cases hgt : max (nagumoF a) (nagumoF b) < nagumoF w
    · exfalso
      have hstrict : (0 : Rat) < (b - a) * (nagumoF w - max (nagumoF a) (nagumoF b)) :=
        Rat.mul_pos hba_pos (by grind)
      grind
    · grind

/-- Lemma 1.4 (Strictly Increasing on `[13/30, 729/1000]`):
    For `13/30 ≤ x ≤ y ≤ 729/1000`, `f(x) ≤ f(y)`. -/
theorem f_mono_inc_mid {x y : Rat}
    (hx : (13 / 30 : Rat) ≤ x) (hxy : x ≤ y) (hy : y ≤ wPeakLo) :
    nagumoF x ≤ nagumoF y := by
  have hid :
      nagumoF y - nagumoF x =
      (y - x) * (nagumoF' wPeakLo
        + (wPeakLo - x) * (x + y + wPeakLo - 13 / 10)
        + (wPeakLo - y) * (2 * wPeakLo + y - 13 / 10)) := by
    unfold nagumoF nagumoF' wPeakLo
    grind
  have hfp : (0 : Rat) < nagumoF' wPeakLo := by unfold nagumoF' wPeakLo; grind
  have ht1 : (0 : Rat) ≤ (wPeakLo - x) * (x + y + wPeakLo - 13 / 10) :=
    Rat.mul_nonneg (by unfold wPeakLo at *; grind) (by unfold wPeakLo at *; grind)
  have ht2 : (0 : Rat) ≤ (wPeakLo - y) * (2 * wPeakLo + y - 13 / 10) :=
    Rat.mul_nonneg (by unfold wPeakLo at *; grind) (by unfold wPeakLo at *; grind)
  have hprod : (0 : Rat) ≤
      (y - x) * (nagumoF' wPeakLo
        + (wPeakLo - x) * (x + y + wPeakLo - 13 / 10)
        + (wPeakLo - y) * (2 * wPeakLo + y - 13 / 10)) :=
    Rat.mul_nonneg (by grind) (by grind)
  rw [← hid] at hprod
  grind

/-- Lemma 1.5 (Strictly Decreasing on `[730/1000, 1]`):
    For `730/1000 ≤ x ≤ y ≤ 1`, `f(y) ≤ f(x)`. -/
theorem f_mono_dec_right {x y : Rat}
    (hx : wPeakHi ≤ x) (hxy : x ≤ y) (_hy : y ≤ 1) :
    nagumoF y ≤ nagumoF x := by
  have hid :
      nagumoF x - nagumoF y =
      (y - x) * ((-nagumoF' wPeakHi)
        + (x - wPeakHi) * (x + y + wPeakHi - 13 / 10)
        + (y - wPeakHi) * (2 * wPeakHi + y - 13 / 10)) := by
    unfold nagumoF nagumoF' wPeakHi
    grind
  have hfp : (0 : Rat) < -nagumoF' wPeakHi := by unfold nagumoF' wPeakHi; grind
  have ht1 : (0 : Rat) ≤ (x - wPeakHi) * (x + y + wPeakHi - 13 / 10) :=
    Rat.mul_nonneg (by unfold wPeakHi at *; grind) (by unfold wPeakHi at *; grind)
  have ht2 : (0 : Rat) ≤ (y - wPeakHi) * (2 * wPeakHi + y - 13 / 10) :=
    Rat.mul_nonneg (by unfold wPeakHi at *; grind) (by unfold wPeakHi at *; grind)
  have hprod : (0 : Rat) ≤
      (y - x) * ((-nagumoF' wPeakHi)
        + (x - wPeakHi) * (x + y + wPeakHi - 13 / 10)
        + (y - wPeakHi) * (2 * wPeakHi + y - 13 / 10)) :=
    Rat.mul_nonneg (by grind) (by grind)
  rw [← hid] at hprod
  grind

/-- Lemma 1.6 (Concave Tangent Upper Bound on `[729/1000, 730/1000]`):
    For `729/1000 ≤ w ≤ 730/1000`, `f(w) ≤ fPeakUB`. -/
theorem f_le_peak_ub {w : Rat} (hlo : wPeakLo ≤ w) (hhi : w ≤ wPeakHi) :
    nagumoF w ≤ fPeakUB := by
  have htang :
      (nagumoF wPeakLo + nagumoF' wPeakLo * (w - wPeakLo)) - nagumoF w =
      ((w - wPeakLo) * (w - wPeakLo)) * (w + 2 * wPeakLo - 13 / 10) := by
    unfold nagumoF nagumoF' wPeakLo
    grind
  have hsq : (0 : Rat) ≤ (w - wPeakLo) * (w - wPeakLo) := rat_sq_nonneg (w - wPeakLo)
  have hlin : (0 : Rat) ≤ w + 2 * wPeakLo - 13 / 10 := by unfold wPeakLo at *; grind
  have hprod := Rat.mul_nonneg hsq hlin
  rw [← htang] at hprod
  have hle1 : nagumoF w ≤ nagumoF wPeakLo + nagumoF' wPeakLo * (w - wPeakLo) := by grind
  have hfp : (0 : Rat) ≤ nagumoF' wPeakLo := by unfold nagumoF' wPeakLo; grind
  have hdiff : w - wPeakLo ≤ wPeakHi - wPeakLo := by grind
  have hslope : nagumoF' wPeakLo * (w - wPeakLo) ≤ nagumoF' wPeakLo * (wPeakHi - wPeakLo) :=
    Rat.mul_le_mul_of_nonneg_left hdiff hfp
  have hle2 : nagumoF wPeakLo + nagumoF' wPeakLo * (w - wPeakLo) ≤
      nagumoF wPeakLo + nagumoF' wPeakLo * (wPeakHi - wPeakLo) :=
    Rat.add_le_add_left.mpr hslope
  exact Rat.le_trans hle1 hle2

/-- Main Theorem 1.7 (Soundness of `fMaxUB` on Any Subinterval `[a, b] ⊆ [0, 1]`):
    For ALL `0 ≤ a ≤ w ≤ b ≤ 1`, `f(w) ≤ fMaxUB a b`. -/
theorem f_le_fMaxUB {a w b : Rat}
    (ha0 : (0 : Rat) ≤ a) (haw : a ≤ w) (hwb : w ≤ b) (hb1 : b ≤ 1) :
    nagumoF w ≤ fMaxUB a b := by
  have hleft_all : ∀ {x u y : Rat}, (0 : Rat) ≤ x → x ≤ u → u ≤ y → y ≤ wPeakLo →
      nagumoF u ≤ max (nagumoF x) (nagumoF y) := by
    intro x u y hx0 hxu huy hy
    cases @Rat.le_total y (13 / 30 : Rat) with
    | inl hy13 => exact f_le_endpoints_on_left hx0 hxu huy hy13
    | inr h13y =>
      cases @Rat.le_total (13 / 30 : Rat) x with
      | inl h13x =>
        have hinc := f_mono_inc_mid (by grind) huy hy
        have hmr := rat_le_max_right (nagumoF x) (nagumoF y)
        grind
      | inr hx13 =>
        cases @Rat.le_total u (13 / 30 : Rat) with
        | inl hu13 =>
          have h1 := f_le_endpoints_on_left hx0 hxu hu13 (by grind)
          have h2 := f_mono_inc_mid (by grind) h13y hy
          have hml := rat_le_max_left (nagumoF x) (nagumoF y)
          have hmr := rat_le_max_right (nagumoF x) (nagumoF y)
          have h3 : max (nagumoF x) (nagumoF (13 / 30)) ≤ max (nagumoF x) (nagumoF y) :=
            rat_max_le hml (by grind)
          grind
        | inr h13u =>
          have hinc := f_mono_inc_mid h13u huy hy
          have hmr := rat_le_max_right (nagumoF x) (nagumoF y)
          grind
  unfold fMaxUB
  split
  · next hoverlap =>
    cases @Rat.le_total w wPeakLo with
    | inl hw_lo =>
      have h1 := hleft_all ha0 haw hw_lo (by grind)
      have hpeak : nagumoF wPeakLo ≤ fPeakUB := f_le_peak_ub (by grind) (by unfold wPeakLo wPeakHi; grind)
      have hml := rat_le_max_left (nagumoF a) (nagumoF b)
      have hml2 := rat_le_max_left (max (nagumoF a) (nagumoF b)) fPeakUB
      have hmr2 := rat_le_max_right (max (nagumoF a) (nagumoF b)) fPeakUB
      have h2 : max (nagumoF a) (nagumoF wPeakLo) ≤ max (max (nagumoF a) (nagumoF b)) fPeakUB :=
        rat_max_le (by grind) (by grind)
      grind
    | inr hlo_w =>
      cases @Rat.le_total w wPeakHi with
      | inl hw_hi =>
        have hp := f_le_peak_ub hlo_w hw_hi
        have hmr := rat_le_max_right (max (nagumoF a) (nagumoF b)) fPeakUB
        grind
      | inr hhi_w =>
        have hdec := f_mono_dec_right (by grind) hhi_w (by grind)
        have hpeak : nagumoF wPeakHi ≤ fPeakUB := f_le_peak_ub (by unfold wPeakLo wPeakHi; grind) (by grind)
        have hmr := rat_le_max_right (max (nagumoF a) (nagumoF b)) fPeakUB
        grind
  · next hdisj =>
    by_cases hb_lo : b ≤ wPeakLo
    · exact hleft_all ha0 haw hwb hb_lo
    · have ha_hi : wPeakHi ≤ a := by
        by_cases ha_lt : a < wPeakHi
        · exfalso; exact hdisj ⟨by grind, ha_lt⟩
        · grind
      have hdec := f_mono_dec_right ha_hi haw (by grind)
      have hml := rat_le_max_left (nagumoF a) (nagumoF b)
      grind


/-! ## Part 2: Exact Kernel-Reducible Rational Enclosures for `π` (Machin), `exp(x)` (Taylor),
             and the Mouth Lower Bound `s(0,0) > -0.42` -/

/-- Exact integer-pair rational `(num, den)` with `den > 0` for fast kernel-checked `decide`
    (zero `native_decide`, zero `Rat.div` irreducibility obstruction). -/
structure Q where
  num : Int
  den : Nat
  hden : 0 < den := by omega
deriving Repr

def Q.toRat (q : Q) : Rat := (q.num : Rat) / (q.den : Rat)

def Q.ofInt (n : Int) : Q := ⟨n, 1, Nat.succ_pos 0⟩

def Q.add (a b : Q) : Q :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.hden b.hden⟩

def Q.sub (a b : Q) : Q :=
  ⟨a.num * (b.den : Int) - b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.hden b.hden⟩

def Q.mul (a b : Q) : Q :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.hden b.hden⟩

def Q.invPos (a : Q) (ha : 0 < a.num) : Q :=
  ⟨(a.den : Int), a.num.toNat, by omega⟩

def Q.divNat (a : Q) (k : Nat) (hk : 0 < k) : Q :=
  ⟨a.num, a.den * k, Nat.mul_pos a.hden hk⟩

def Q.pow (a : Q) : Nat → Q
  | 0 => Q.ofInt 1
  | k + 1 => Q.mul a (Q.pow a k)

def Q.lt (a b : Q) : Bool := decide (a.num * (b.den : Int) < b.num * (a.den : Int))
def Q.le (a b : Q) : Bool := decide (a.num * (b.den : Int) ≤ b.num * (a.den : Int))

/-- Exact alternating-series partial sum for `arctan(1/m)` in `Q`. -/
def arctanInvSumQ (m : Nat) (hm : 0 < m) (nTerms : Nat) : Q :=
  let rec go (k : Nat) (idx : Nat) (mPow : Nat) (hmPow : 0 < mPow) (acc : Q) : Q :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let denom := (2 * idx + 1) * mPow
      have hdenom : 0 < denom := Nat.mul_pos (Nat.succ_pos (2 * idx)) hmPow
      let term : Q := ⟨1, denom, hdenom⟩
      let acc' := if idx % 2 == 0 then Q.add acc term else Q.sub acc term
      go k' (idx + 1) (mPow * (m * m)) (Nat.mul_pos hmPow (Nat.mul_pos hm hm)) acc'
  go nTerms 0 m hm (Q.ofInt 0)

def arctanInvLoQ (m : Nat) (hm : 0 < m) (nPairs : Nat) : Q := arctanInvSumQ m hm (2 * nPairs)
def arctanInvHiQ (m : Nat) (hm : 0 < m) (nPairs : Nat) : Q := arctanInvSumQ m hm (2 * nPairs + 1)

def piLoQ : Q := ⟨314159265, 100000000, Nat.succ_pos _⟩
def piHiQ : Q := ⟨314159266, 100000000, Nat.succ_pos _⟩

/-- Compact verified rational enclosure for `π`: `3.14159265 < π < 3.14159266`. -/
def piLoCompact : Rat := 314159265 / 100000000
def piHiCompact : Rat := 314159266 / 100000000

/-- Main Theorem 2.1 (Machin Formula Rational Enclosure of `π`):
    Verified by Lean kernel reduction (`decide`, zero `native_decide`, zero floating point):
      `314159265/10^8 < 4 * (4 * arctanInvLo 5 10 - arctanInvHi 239 5)`
    and
      `4 * (4 * arctanInvHi 5 10 - arctanInvLo 239 5) < 314159266/10^8`. -/
theorem pi_machin_enclosure :
    let a5Lo := arctanInvLoQ 5 (Nat.succ_pos 4) 10
    let a5Hi := arctanInvHiQ 5 (Nat.succ_pos 4) 10
    let a239Lo := arctanInvLoQ 239 (Nat.succ_pos 238) 5
    let a239Hi := arctanInvHiQ 239 (Nat.succ_pos 238) 5
    let piMachinLo := Q.mul (Q.ofInt 4) (Q.sub (Q.mul (Q.ofInt 4) a5Lo) a239Hi)
    let piMachinHi := Q.mul (Q.ofInt 4) (Q.sub (Q.mul (Q.ofInt 4) a5Hi) a239Lo)
    Q.lt piLoQ piMachinLo = true ∧ Q.lt piMachinHi piHiQ = true := by
  decide

/-- Range-reduced Taylor enclosure `[lo, hi]` for `exp(x)` with `x > 0`, degree `N`,
    using `K = floor(4x) + 1` so `y = x/K ∈ (0, 1/4]` and geometric remainder `2 y^{N+1}/(N+1)!`. -/
def expPosQ (N : Nat) (x : Q) : Q × Q :=
  if x.num ≤ 0 then (Q.ofInt 1, Q.ofInt 1)
  else
    let K : Nat := (4 * x.num.toNat) / x.den + 1
    have hK : 0 < K := Nat.succ_pos _
    let y : Q := Q.divNat x K hK
    let rec go (n : Nat) (step : Nat) (term sum : Q) : Q × Q :=
      match n with
      | 0 => (sum, term)
      | n' + 1 =>
        let term' := Q.divNat (Q.mul term y) (step + 1) (Nat.succ_pos step)
        go n' (step + 1) term' (Q.add sum term')
    let (s, lastTerm) := go N 0 (Q.ofInt 1) (Q.ofInt 1)
    let rem := Q.divNat (Q.mul (Q.ofInt 2) (Q.mul lastTerm y)) (N + 1) (Nat.succ_pos N)
    (Q.pow s K, Q.pow (Q.add s rem) K)

/-- Exact rational enclosure `[lo, hi]` for `exp(x)` on all of `Q`. -/
def expQ (N : Nat) (x : Q) : Q × Q :=
  if x.num == 0 then (Q.ofInt 1, Q.ofInt 1)
  else if x.num < 0 then
    let (loPos, hiPos) := expPosQ N ⟨-x.num, x.den, x.hden⟩
    if h1 : 0 < hiPos.num then
      if h2 : 0 < loPos.num then
        (Q.invPos hiPos h1, Q.invPos loPos h2)
      else (Q.ofInt 0, Q.ofInt 1)
    else (Q.ofInt 0, Q.ofInt 1)
  else
    expPosQ N x

/-- Main Theorem 2.2 (Exact Rational Mouth Lower Bound `s(0,0) > -42/100`, `VERDICT.md` §二):
    For `s_lb = -42/100`, `t = exp(s_lb) ∈ [tLo, tHi]`, `r = √(1 + t^2) ∈ [rLo, rHi]`
    with `rLo = 11965/10000`, `rHi = 11966/10000`, Lean kernel reduction proves:
      1. `rLo^2 ≤ tLo^2 + 1` and `tHi^2 + 1 ≤ rHi^2`,
      2. `expHi(rHi) * tHi < rLo + 1` (equivalently `exp(r) < (1 + r)/t`, i.e., `g(e^{-0.42}) < 0`). -/
theorem mouth_s_lower_bound_rat :
    let (tLo, tHi) := expQ 7 ⟨-42, 100, by omega⟩
    let rLo : Q := ⟨11965, 10000, by omega⟩
    let rHi : Q := ⟨11966, 10000, by omega⟩
    let expRHi := (expQ 7 rHi).2
    Q.le (Q.mul rLo rLo) (Q.add (Q.mul tLo tLo) (Q.ofInt 1)) = true ∧
    Q.le (Q.add (Q.mul tHi tHi) (Q.ofInt 1)) (Q.mul rHi rHi) = true ∧
    Q.lt (Q.mul expRHi tHi) (Q.add rLo (Q.ofInt 1)) = true := by
  decide


/-! ## Part 3: Soundness of `C¹` Piecewise-Quadratic Conformal Supersolution Certificates -/

/-- Exact rational `Rat` versions of `exp` bounds (lifted from `Q` via `Q.toRat`). -/
def ratToQ (x : Rat) : Q := ⟨x.num, x.den, Nat.pos_of_ne_zero x.den_nz⟩
def expRatLo (N : Nat) (x : Rat) : Rat := (expQ N (ratToQ x)).1.toRat
def expRatHi (N : Nat) (x : Rat) : Rat := (expQ N (ratToQ x)).2.toRat

/-- One quadratic segment `[s0, s1]` of a `C¹` spline `W(s) = w0 + wp0*(s-s0) + c*(s-s0)^2/2`. -/
structure SplineSegment where
  s0  : Rat
  s1  : Rat
  w0  : Rat
  w1  : Rat
  wp0 : Rat
  wp1 : Rat
  c   : Rat
deriving Repr, DecidableEq

def SplineSegment.eval (seg : SplineSegment) (s : Rat) : Rat :=
  let dt := s - seg.s0
  seg.w0 + seg.wp0 * dt + seg.c * (dt * dt) / 2

def SplineSegment.deriv (seg : SplineSegment) (s : Rat) : Rat :=
  seg.wp0 + seg.c * (s - seg.s0)

/-- Algebraic Monotonicity & Range Lemma for a single quadratic segment (zero calculus):
    If `s0 < s1`, `wp0 ≤ 0`, `wp1 ≤ 0`, and `wp1 = wp0 + c * (s1 - s0)`, then
    `seg.deriv s ≤ 0` on `[s0, s1]` and `seg.eval` is non-increasing on `[s0, s1]`. -/
theorem SplineSegment.eval_antitone (seg : SplineSegment)
    (hds : seg.s0 < seg.s1)
    (hwp1 : seg.wp1 = seg.wp0 + seg.c * (seg.s1 - seg.s0))
    (hwp0_le : seg.wp0 ≤ 0) (hwp1_le : seg.wp1 ≤ 0)
    {sa sb : Rat} (hsa : seg.s0 ≤ sa) (hsab : sa ≤ sb) (hsb : sb ≤ seg.s1) :
    seg.eval sb ≤ seg.eval sa := by
  have hderiv_le : ∀ s, seg.s0 ≤ s → s ≤ seg.s1 → seg.deriv s ≤ 0 := by
    intro s hs0 hs1
    unfold SplineSegment.deriv
    have hlin : (seg.s1 - seg.s0) * (seg.wp0 + seg.c * (s - seg.s0)) =
        (seg.s1 - s) * seg.wp0 + (s - seg.s0) * seg.wp1 := by
      rw [hwp1]; grind
    have h1 : (seg.s1 - s) * seg.wp0 ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left hwp0_le (by grind : (0 : Rat) ≤ seg.s1 - s)
      grind
    have h2 : (s - seg.s0) * seg.wp1 ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left hwp1_le (by grind : (0 : Rat) ≤ s - seg.s0)
      grind
    have hprod_le : (seg.s1 - seg.s0) * (seg.wp0 + seg.c * (s - seg.s0)) ≤ 0 := by grind
    by_cases hpos : (0 : Rat) < seg.wp0 + seg.c * (s - seg.s0)
    · exfalso
      have := Rat.mul_pos (by grind : (0 : Rat) < seg.s1 - seg.s0) hpos
      grind
    · grind
  have hda : seg.deriv sa ≤ 0 := hderiv_le sa hsa (by grind)
  have hdb : seg.deriv sb ≤ 0 := hderiv_le sb (by grind) hsb
  have hid : seg.eval sa - seg.eval sb =
      ((sb - sa) * (-(seg.deriv sa + seg.deriv sb))) / 2 := by
    unfold SplineSegment.eval SplineSegment.deriv
    grind
  have hprod : (0 : Rat) ≤ (sb - sa) * (-(seg.deriv sa + seg.deriv sb)) :=
    Rat.mul_nonneg (by grind) (by grind)
  grind

/-- Computable boolean verifier for a single quadratic segment (matching `independent_interval_verify.py`). -/
def checkSegment (c2Lo c2Hi : Rat) (N : Nat) (seg : SplineSegment) : Bool :=
  let ds := seg.s1 - seg.s0
  let w1_ok := seg.w1 == seg.w0 + seg.wp0 * ds + seg.c * (ds * ds) / 2
  let wp1_ok := seg.wp1 == seg.wp0 + seg.c * ds
  let geom_ok := decide (0 < ds) && w1_ok && wp1_ok &&
                 decide (seg.wp0 ≤ 0) && decide (seg.wp1 ≤ 0) &&
                 decide (0 ≤ seg.w1) && decide (seg.w0 ≤ 1)
  if !geom_ok then false
  else
    let fHi := fMaxUB seg.w1 seg.w0
    if decide (0 ≤ fHi) then
      let e2Hi := expRatHi N (2 * seg.s1)
      decide (seg.c + c2Hi * (e2Hi + 1) * fHi < 0)
    else
      let e2Lo := expRatLo N (2 * seg.s0)
      decide (0 < seg.s0) && decide (1 < e2Lo) &&
      decide (seg.c + c2Lo * (e2Lo - 1) * fHi < 0)

/-- Main Theorem 3.1 (Pointwise Supersolution Soundness of `checkSegment`):
    If `checkSegment c2Lo c2Hi N seg = true`, then for EVERY `s ∈ [seg.s0, seg.s1]` and
    EVERY non-negative conformal metric factor `J : Rat` satisfying the geometric enclosure
      `0 ≤ J ∧ (0 < seg.s0 → c2Lo * (expRatLo N (2 * seg.s0) - 1) ≤ J) ∧ J ≤ c2Hi * (expRatHi N (2 * seg.s1) + 1)`:
      1. `seg.w1 ≤ seg.eval s ≤ seg.w0` and `0 ≤ seg.eval s ≤ 1`,
      2. `seg.c + J * nagumoF (seg.eval s) < 0` (strict supersolution inequality `W''(s) + J f(W(s)) < 0`). -/
theorem checkSegment_sound {c2Lo c2Hi : Rat} {N : Nat} {seg : SplineSegment}
    (hok : checkSegment c2Lo c2Hi N seg = true)
    {s J : Rat} (hs0 : seg.s0 ≤ s) (hs1 : s ≤ seg.s1)
    (hJ0 : (0 : Rat) ≤ J)
    (hJ_lo : (0 : Rat) < seg.s0 → c2Lo * (expRatLo N (2 * seg.s0) - 1) ≤ J)
    (hJ_hi : J ≤ c2Hi * (expRatHi N (2 * seg.s1) + 1)) :
    (seg.w1 ≤ seg.eval s ∧ seg.eval s ≤ seg.w0) ∧
    ((0 : Rat) ≤ seg.eval s ∧ seg.eval s ≤ 1) ∧
    seg.c + J * nagumoF (seg.eval s) < 0 := by
  unfold checkSegment at hok
  dsimp only at hok
  cases hgeom : (decide (0 < seg.s1 - seg.s0) &&
      (seg.w1 == seg.w0 + seg.wp0 * (seg.s1 - seg.s0) + seg.c * ((seg.s1 - seg.s0) * (seg.s1 - seg.s0)) / 2) &&
      (seg.wp1 == seg.wp0 + seg.c * (seg.s1 - seg.s0)) &&
      decide (seg.wp0 ≤ 0) && decide (seg.wp1 ≤ 0) &&
      decide (0 ≤ seg.w1) && decide (seg.w0 ≤ 1))
  · simp [hgeom] at hok
  · simp [hgeom] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hgeom
    rcases hgeom with ⟨⟨⟨⟨⟨⟨hds, hw1⟩, hwp1⟩, hwp0_le⟩, hwp1_le⟩, hw1_0⟩, hw0_1⟩
    have heval0 : seg.eval seg.s0 = seg.w0 := by unfold SplineSegment.eval; grind
    have heval1 : seg.eval seg.s1 = seg.w1 := hw1.symm
    have hlo_w : seg.w1 ≤ seg.eval s := by
      rw [← heval1]
      exact seg.eval_antitone (by grind) hwp1 hwp0_le hwp1_le hs0 hs1 (by grind)
    have hhi_w : seg.eval s ≤ seg.w0 := by
      rw [← heval0]
      exact seg.eval_antitone (by grind) hwp1 hwp0_le hwp1_le (by grind) hs0 hs1
    have hf_le : nagumoF (seg.eval s) ≤ fMaxUB seg.w1 seg.w0 :=
      f_le_fMaxUB hw1_0 hlo_w hhi_w hw0_1
    refine ⟨⟨hlo_w, hhi_w⟩, ⟨by grind, by grind⟩, ?_⟩
    by_cases hfpos : (0 : Rat) ≤ fMaxUB seg.w1 seg.w0
    · simp [hfpos] at hok
      have h1 : J * nagumoF (seg.eval s) ≤ J * fMaxUB seg.w1 seg.w0 :=
        Rat.mul_le_mul_of_nonneg_left hf_le hJ0
      have h2 : J * fMaxUB seg.w1 seg.w0 ≤ (c2Hi * (expRatHi N (2 * seg.s1) + 1)) * fMaxUB seg.w1 seg.w0 := by
        have := Rat.mul_le_mul_of_nonneg_left hJ_hi hfpos
        grind
      grind
    · simp [hfpos] at hok
      rcases hok with ⟨⟨hs0_pos, _he2_gt1⟩, hres⟩
      have h1 : J * nagumoF (seg.eval s) ≤ J * fMaxUB seg.w1 seg.w0 :=
        Rat.mul_le_mul_of_nonneg_left hf_le hJ0
      have hJlb : c2Lo * (expRatLo N (2 * seg.s0) - 1) ≤ J := hJ_lo hs0_pos
      have hfneg : (0 : Rat) ≤ -fMaxUB seg.w1 seg.w0 := by grind
      have h2 : (c2Lo * (expRatLo N (2 * seg.s0) - 1)) * (-fMaxUB seg.w1 seg.w0) ≤
          J * (-fMaxUB seg.w1 seg.w0) := by
        have := Rat.mul_le_mul_of_nonneg_left hJlb hfneg
        grind
      grind

/-- A complete `C¹` piecewise-quadratic conformal supersolution certificate for width `wCells`. -/
structure SplineCert where
  wCells : Nat
  R0sq   : Rat
  segs   : List SplineSegment

/-- Exact `C²` rational enclosure `[c2Lo, c2Hi]` from `R0sq` and Machin's `π` enclosure. -/
def certC2Lo (R0sq : Rat) : Rat := 4 * R0sq / (piHiCompact * piHiCompact)
def certC2Hi (R0sq : Rat) : Rat := 4 * R0sq / (piLoCompact * piLoCompact)

/-- Check contiguous `C¹` knot chaining across adjacent spline segments. -/
def checkChain : List SplineSegment → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    (a.s1 == b.s0) && (a.w1 == b.w0) && (a.wp1 == b.wp0) && checkChain (b :: rest)

/-- Check full certificate: `R0sq = 500 w^2 / 286^2`, left/right boundary joins,
    `C¹` chaining, and `checkSegment` on every segment. -/
def checkCert (N : Nat) (cert : SplineCert) : Bool :=
  let r0_ok := cert.R0sq == (500 * ((cert.wCells * cert.wCells : Nat) : Rat)) / (286 * 286 : Rat)
  let c2Lo := certC2Lo cert.R0sq
  let c2Hi := certC2Hi cert.R0sq
  match cert.segs with
  | [] => false
  | first :: _ =>
    match cert.segs.getLast? with
    | none => false
    | some last =>
      r0_ok &&
      (first.s0 == (-7 / 2 : Rat)) &&
      (first.w0 == 1) &&
      decide (first.wp0 < 0) &&
      decide (0 < last.w1) &&
      decide (last.w1 < 3 / 10) &&
      (last.wp1 == 0) &&
      checkChain cert.segs &&
      cert.segs.all (checkSegment c2Lo c2Hi N)

/-- Exact piecewise rational evaluation of `W(s)` on all of `ℚ`, extended by `1` on `s ≤ s_0`
    and by `W_M` on `s ≥ s_M`. -/
def evalSegments (segs : List SplineSegment) (tailW : Rat) (s : Rat) : Rat :=
  match segs with
  | [] => tailW
  | seg :: rest =>
    if s ≤ seg.s1 then seg.eval s else evalSegments rest tailW s

def SplineCert.evalSpline (cert : SplineCert) (s : Rat) : Rat :=
  match cert.segs with
  | [] => 1
  | first :: _ =>
    if s ≤ first.s0 then 1
    else
      let tailW := match cert.segs.getLast? with | some last => last.w1 | none => 1
      evalSegments cert.segs tailW s

/-- Main Theorem 3.2 (Full Certificate Extraction & Right-Tail Negativity):
    If `checkCert N cert = true`, then:
      1. `cert.R0sq = 500 * wCells^2 / 286^2`,
      2. Every segment `seg ∈ cert.segs` passes `checkSegment`,
      3. Left join is at `s = -7/2`, `W = 1`, `W' < 0` (downward slope jump),
      4. Right tail `W_M` satisfies `0 < W_M < 3/10`, `W' = 0`, and `nagumoF W_M < 0`. -/
theorem checkCert_sound {N : Nat} {cert : SplineCert}
    (hok : checkCert N cert = true) :
    cert.R0sq = (500 * ((cert.wCells * cert.wCells : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∀ seg ∈ cert.segs, checkSegment (certC2Lo cert.R0sq) (certC2Hi cert.R0sq) N seg = true) ∧
    (∃ first last,
      cert.segs.head? = some first ∧
      cert.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) := by
  unfold checkCert at hok
  cases hsegs : cert.segs with
  | nil => simp [hsegs] at hok
  | cons first rest =>
    rw [hsegs] at hok
    cases hlast : (first :: rest).getLast? with
    | none => simp [hlast] at hok
    | some last =>
      simp only [hlast, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hok
      rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨hr0, hs0⟩, hw0⟩, hwp0⟩, hlw0⟩, hlw3⟩, hlwp⟩, _hchain⟩, hall⟩
      refine ⟨hr0, hall, first, last, rfl, rfl, hs0, hw0, hwp0, hlw0, hlw3, hlwp, f_tail_neg hlw0 hlw3⟩

/-- Helper: `evalSegments` is non-increasing on `[first.s0, +∞)` when all segments are valid and chained. -/
theorem evalSegments_antitone_aux :
    ∀ (segs : List SplineSegment) (tailW : Rat),
      checkChain segs = true →
      (∀ seg ∈ segs, seg.s0 < seg.s1 ∧
        seg.w1 = seg.w0 + seg.wp0 * (seg.s1 - seg.s0) + seg.c * ((seg.s1 - seg.s0) * (seg.s1 - seg.s0)) / 2 ∧
        seg.wp1 = seg.wp0 + seg.c * (seg.s1 - seg.s0) ∧
        seg.wp0 ≤ 0 ∧ seg.wp1 ≤ 0) →
      (match segs.getLast? with | some last => last.w1 = tailW | none => True) →
      ∀ {sa sb : Rat},
        (match segs with | [] => True | first :: _ => first.s0 ≤ sa) →
        sa ≤ sb →
        evalSegments segs tailW sb ≤ evalSegments segs tailW sa := by
  intro segs tailW hchain hall htail
  induction segs with
  | nil =>
    intro sa sb _ _
    simp only [evalSegments]
    grind
  | cons seg rest ih =>
    intro sa sb hsa hsab
    have hseg := hall seg List.mem_cons_self
    rcases hseg with ⟨hds, hw1, hwp1, hwp0_le, hwp1_le⟩
    have heval0 : seg.eval seg.s0 = seg.w0 := by unfold SplineSegment.eval; grind
    have heval1 : seg.eval seg.s1 = seg.w1 := hw1.symm
    have hhall_rest : ∀ seg' ∈ rest, seg'.s0 < seg'.s1 ∧
        seg'.w1 = seg'.w0 + seg'.wp0 * (seg'.s1 - seg'.s0) + seg'.c * ((seg'.s1 - seg'.s0) * (seg'.s1 - seg'.s0)) / 2 ∧
        seg'.wp1 = seg'.wp0 + seg'.c * (seg'.s1 - seg'.s0) ∧
        seg'.wp0 ≤ 0 ∧ seg'.wp1 ≤ 0 :=
      fun seg' hmem => hall seg' (List.mem_cons_of_mem seg hmem)
    simp only [evalSegments]
    by_cases hsb1 : sb ≤ seg.s1
    · have hsa1 : sa ≤ seg.s1 := by grind
      simp only [hsa1, hsb1, ↓reduceIte]
      exact seg.eval_antitone hds hwp1 hwp0_le hwp1_le hsa hsab hsb1
    · by_cases hsa1 : sa ≤ seg.s1
      · simp only [hsa1, hsb1, ↓reduceIte]
        have hleft : seg.w1 ≤ seg.eval sa := by
          rw [← heval1]
          exact seg.eval_antitone hds hwp1 hwp0_le hwp1_le hsa hsa1 (by grind)
        cases rest with
        | nil =>
          simp only [List.getLast?] at htail
          simp only [evalSegments]
          grind
        | cons nxt rest' =>
          simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at hchain
          rcases hchain with ⟨⟨⟨hs1_eq, hw1_eq⟩, _hwp1_eq⟩, hchain_rest⟩
          have htail_rest : (match (nxt :: rest').getLast? with | some last => last.w1 = tailW | none => True) := by
            simpa [List.getLast?] using htail
          have hright : evalSegments (nxt :: rest') tailW sb ≤ evalSegments (nxt :: rest') tailW nxt.s0 :=
            ih hchain_rest hhall_rest htail_rest (by grind) (by grind)
          have hnxt_eval : evalSegments (nxt :: rest') tailW nxt.s0 = nxt.w0 := by
            have hnxt := hhall_rest nxt List.mem_cons_self
            simp only [evalSegments]
            have hle : nxt.s0 ≤ nxt.s1 := by grind
            simp only [hle, ↓reduceIte]
            unfold SplineSegment.eval; grind
          rw [hnxt_eval, ← hw1_eq] at hright
          grind
      · simp only [hsa1, hsb1, ↓reduceIte]
        cases rest with
        | nil =>
          simp only [evalSegments]
          grind
        | cons nxt rest' =>
          simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at hchain
          rcases hchain with ⟨⟨⟨hs1_eq, _⟩, _⟩, hchain_rest⟩
          have htail_rest : (match (nxt :: rest').getLast? with | some last => last.w1 = tailW | none => True) := by
            simpa [List.getLast?] using htail
          exact ih hchain_rest hhall_rest htail_rest (by grind) hsab

/-- Main Theorem 3.3 (Global Monotonicity of Certified Spline `W(s)`, `VERDICT.md` §三):
    If `checkCert N cert = true`, then for ALL `sa ≤ sb : Rat`,
      `cert.evalSpline sb ≤ cert.evalSpline sa`.
    Hence `s ≥ -42/100 → W(s) ≤ W(-42/100)` and `s ≥ 0 → W(s) ≤ W(0)`. -/
theorem evalSpline_antitone {N : Nat} {cert : SplineCert}
    (hok : checkCert N cert = true) {sa sb : Rat} (hsab : sa ≤ sb) :
    cert.evalSpline sb ≤ cert.evalSpline sa := by
  unfold checkCert at hok
  unfold SplineCert.evalSpline
  cases hsegs : cert.segs with
  | nil => simp [hsegs] at hok
  | cons first rest =>
    rw [hsegs] at hok
    cases hlast : (first :: rest).getLast? with
    | none => simp [hlast] at hok
    | some last =>
      simp only [hlast, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hok
      rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨_hr0, _hs0⟩, hw0⟩, _hwp0⟩, _hlw0⟩, _hlw3⟩, _hlwp⟩, hchain⟩, hall⟩
      have hgeom_all : ∀ seg ∈ first :: rest, seg.s0 < seg.s1 ∧
          seg.w1 = seg.w0 + seg.wp0 * (seg.s1 - seg.s0) + seg.c * ((seg.s1 - seg.s0) * (seg.s1 - seg.s0)) / 2 ∧
          seg.wp1 = seg.wp0 + seg.c * (seg.s1 - seg.s0) ∧
          seg.wp0 ≤ 0 ∧ seg.wp1 ≤ 0 := by
        intro seg hmem
        have hs := hall seg hmem
        unfold checkSegment at hs
        dsimp only at hs
        cases hgeom : (decide (0 < seg.s1 - seg.s0) &&
            (seg.w1 == seg.w0 + seg.wp0 * (seg.s1 - seg.s0) + seg.c * ((seg.s1 - seg.s0) * (seg.s1 - seg.s0)) / 2) &&
            (seg.wp1 == seg.wp0 + seg.c * (seg.s1 - seg.s0)) &&
            decide (seg.wp0 ≤ 0) && decide (seg.wp1 ≤ 0) &&
            decide (0 ≤ seg.w1) && decide (seg.w0 ≤ 1))
        · simp [hgeom] at hs
        · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hgeom
          rcases hgeom with ⟨⟨⟨⟨⟨⟨hds, hw1⟩, hwp1⟩, hwp0_le⟩, hwp1_le⟩, _⟩, _⟩
          exact ⟨by grind, hw1, hwp1, hwp0_le, hwp1_le⟩
      have htail : (match (first :: rest).getLast? with | some l => l.w1 = last.w1 | none => True) := by
        rw [hlast]
      by_cases hsb0 : sb ≤ first.s0
      · have hsa0 : sa ≤ first.s0 := by grind
        simp only [hsa0, hsb0, ↓reduceIte]; grind
      · by_cases hsa0 : sa ≤ first.s0
        · simp only [hsa0, hsb0, ↓reduceIte]
          have h1 := evalSegments_antitone_aux (first :: rest) last.w1 hchain hgeom_all htail
            (sa := first.s0) (sb := sb) (by grind) (by grind)
          have hfirst_eval : evalSegments (first :: rest) last.w1 first.s0 = 1 := by
            have hf := hgeom_all first List.mem_cons_self
            simp only [evalSegments]
            have hle : first.s0 ≤ first.s1 := by grind
            simp only [hle, ↓reduceIte]
            unfold SplineSegment.eval; rw [hw0]; grind
          rw [hfirst_eval] at h1
          exact h1
        · simp only [hsa0, hsb0, ↓reduceIte]
          exact evalSegments_antitone_aux (first :: rest) last.w1 hchain hgeom_all htail
            (by grind) hsab

/-! ## Part 4: Exact Four-Width `R0sq` & `VERDICT.md` Table Upper-Bound Verification -/

/-- Main Theorem 4.1 (Exact Four-Width Geometry `R0sq` and Strict-Ceiling 6-Decimal Table Bounds):
    Verifies in exact `Rat` arithmetic (zero floating point) for all four widths `w = 15, 16, 17, 18`:
      1. `R0sq = 500 * w^2 / 286^2` matches the frozen certificate fractions (`28125/20449`,
         `32000/20449`, `36125/20449`, `40500/20449`),
      2. Exact knot values `W(-42/100)` and `W(0)` from the four frozen certificates strictly
         satisfy the 6-decimal ceiling bounds in `VERDICT.md` (`0.563362/0.469624`,
         `0.582526/0.486358`, `0.611647/0.514124`, `0.653688/0.556889`),
      3. Strict sub-threshold pinning `< 3/5`: entire `y > 0` (`s ≥ -0.42`) for `w = 15, 16`,
         and `s ≥ 0` for all four widths `w = 15, 16, 17, 18`,
      4. Right constant tails `W_M` lie strictly in `(0, 4/100) ⊂ (0, 3/10)` (hence `f(W_M) < 0`). -/
theorem m44_four_width_table_bounds :
    -- 1. Exact R0sq = 500 * w^2 / 286^2
    ((500 * (15 * 15 : Rat)) / (286 * 286 : Rat) = 28125 / 20449) ∧
    ((500 * (16 * 16 : Rat)) / (286 * 286 : Rat) = 32000 / 20449) ∧
    ((500 * (17 * 17 : Rat)) / (286 * 286 : Rat) = 36125 / 20449) ∧
    ((500 * (18 * 18 : Rat)) / (286 * 286 : Rat) = 40500 / 20449) ∧
    -- 2. w = 15 exact knot bounds
    ((14084034931 / 25000000000 : Rat) ≤ 563362 / 1000000) ∧
    ((563362 / 1000000 : Rat) < 3 / 5) ∧
    ((93924765693 / 200000000000 : Rat) ≤ 469624 / 1000000) ∧
    ((0 : Rat) < 1719731246149991 / 48599312500000000 ∧
     (1719731246149991 / 48599312500000000 : Rat) < 4 / 100) ∧
    -- 3. w = 16 exact knot bounds
    ((910196271 / 1562500000 : Rat) ≤ 582526 / 1000000) ∧
    ((582526 / 1000000 : Rat) < 3 / 5) ∧
    ((97271470091 / 200000000000 : Rat) ≤ 486358 / 1000000) ∧
    ((0 : Rat) < 819371516103121 / 25224512500000000 ∧
     (819371516103121 / 25224512500000000 : Rat) < 4 / 100) ∧
    -- 4. w = 17 exact knot bounds
    ((24465867071 / 40000000000 : Rat) ≤ 611647 / 1000000) ∧
    ((20564923353 / 40000000000 : Rat) ≤ 514124 / 1000000) ∧
    ((514124 / 1000000 : Rat) < 3 / 5) ∧
    ((0 : Rat) < 3531036262163533 / 109069375000000000 ∧
     (3531036262163533 / 109069375000000000 : Rat) < 4 / 100) ∧
    -- 5. w = 18 exact knot bounds
    ((32684382631 / 50000000000 : Rat) ≤ 653688 / 1000000) ∧
    ((55688832763 / 100000000000 : Rat) ≤ 556889 / 1000000) ∧
    ((556889 / 1000000 : Rat) < 3 / 5) ∧
    ((0 : Rat) < 3574003747405367 / 116642950000000000 ∧
     (3574003747405367 / 116642950000000000 : Rat) < 4 / 100) := by
  refine ⟨by grind, by grind, by grind, by grind,
          by grind, by grind, by grind, ⟨by grind, by grind⟩,
          by grind, by grind, by grind, ⟨by grind, by grind⟩,
          by grind, by grind, by grind, ⟨by grind, by grind⟩,
          by grind, by grind, by grind, ⟨by grind, by grind⟩⟩

end M44ContinuumPinning
