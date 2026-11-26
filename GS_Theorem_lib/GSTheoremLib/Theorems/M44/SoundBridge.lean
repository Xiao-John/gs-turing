/-
  End-to-End Soundness Bridge (`M44SoundBridge`):
    Lifts the fast pure-integer kernel verifier `checkFullRawCert` (used on all 2,269 segments
    of M44CertW15..W18) directly to exact `Rat` mathematical theorems:
      1. Exact `QPair → Rat` homomorphisms (`qpEq`, `qpLe`, `qpLt`, `qpAdd`, `qpSub`, `qpMul`,
         `qpNagumoF`, `qpFMaxUB`, `rawC2Lo`, `rawC2Hi`),
      2. Soundness of `expGridList` against any abstract exponential `E : Int → Rat`
         satisfying `E 0 = 1`, `E(k±1) = E(k) * E(±1)`, and `e50_step_enclosure`,
      3. `checkRawSegWithGrid_sound`: strict pointwise PDE supersolution inequality
         `W''(s) + J * f(W(s)) < 0` for all `s ∈ [s0, s1]` and all enclosed conformal scales `J`,
      4. `checkFullRawCert_sound`: global monotonicity `W(sb) ≤ W(sa)`, global upper bounds
         `∀ s ≥ -42/100, W(s) ≤ uMouth` and `∀ s ≥ 0, W(s) ≤ uS0`, boundary joins, and
         pointwise supersolution inequality on every segment of the certified spline.
  Zero external dependencies (pure Lean 4.36.0 `Init`), zero `sorry`, zero custom axioms.
-/
import GSTheoremLib.Theorems.M44.CertCheck

namespace M44ContinuumPinning

/-! ## Part 1: Exact `QPair → Rat` Homomorphisms -/

def QPair.toRat (p : QPair) : Rat := (p.1 : Rat) / (p.2 : Rat)

def RawSeg.toSpline (seg : RawSeg) : SplineSegment :=
  ⟨seg.s0.toRat, seg.s1.toRat, seg.w0.toRat, seg.w1.toRat, seg.wp0.toRat, seg.wp1.toRat, seg.c.toRat⟩

private theorem natCast_pos_rat {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => grind
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hcast : ((m + 2 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by grind
      grind

private theorem intCast_natCast_rat (n : Nat) : ((n : Int) : Rat) = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : (((k + 1 : Nat) : Int) : Rat) = ((k : Int) : Rat) + 1 := by grind
    have h2 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h1, h2, ih]

private theorem intCast_ofNat_rat (n : Nat) : ((Int.ofNat n : Int) : Rat) = (n : Rat) := by
  change ((n : Int) : Rat) = (n : Rat)
  exact intCast_natCast_rat n

private theorem intCast_negSucc_rat (n : Nat) : ((Int.negSucc n : Int) : Rat) = -((n + 1 : Nat) : Rat) := by
  have h1 : (Int.negSucc n : Int) = -((n + 1 : Nat) : Int) := by omega
  rw [h1]
  have h2 : ((-((n + 1 : Nat) : Int) : Int) : Rat) = -(((n + 1 : Nat) : Int) : Rat) := by grind
  rw [h2, intCast_natCast_rat]

private theorem intCast_rat_eq_iff {a b : Int} : (a : Rat) = (b : Rat) ↔ a = b := by
  constructor
  · intro h
    have : ((a - b : Int) : Rat) = 0 := by
      have hsub : ((a - b : Int) : Rat) = (a : Rat) - (b : Rat) := by grind
      rw [hsub, h]; grind
    cases hd : a - b with
    | ofNat n =>
      rw [hd] at this
      cases n with
      | zero =>
        change a - b = (0 : Int) at hd; omega
      | succ m =>
        have hp : (0 : Rat) < ((m + 1 : Nat) : Rat) := natCast_pos_rat (Nat.succ_pos m)
        rw [intCast_ofNat_rat] at this; grind
    | negSucc n =>
      rw [hd] at this
      have hp : (0 : Rat) < ((n + 1 : Nat) : Rat) := natCast_pos_rat (Nat.succ_pos n)
      rw [intCast_negSucc_rat] at this; grind
  · intro h; rw [h]

private theorem intCast_rat_le_iff {a b : Int} : (a : Rat) ≤ (b : Rat) ↔ a ≤ b := by
  constructor
  · intro h
    cases hd : b - a with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast] at hd; omega
    | negSucc n =>
      exfalso
      have hsub : ((b - a : Int) : Rat) = (b : Rat) - (a : Rat) := by grind
      rw [hd, intCast_negSucc_rat] at hsub
      have hp : (0 : Rat) < ((n + 1 : Nat) : Rat) := natCast_pos_rat (Nat.succ_pos n)
      grind
  · intro h
    have hd : ∃ n : Nat, b - a = Int.ofNat n := ⟨(b - a).toNat, by rw [Int.ofNat_eq_natCast]; omega⟩
    rcases hd with ⟨n, hn⟩
    have hsub : ((b - a : Int) : Rat) = (b : Rat) - (a : Rat) := by grind
    rw [hn, intCast_ofNat_rat] at hsub
    have hnn : (0 : Rat) ≤ (n : Rat) := by
      cases n with
      | zero => grind
      | succ m => have := natCast_pos_rat (Nat.succ_pos m); grind
    grind

private theorem intCast_rat_lt_iff {a b : Int} : (a : Rat) < (b : Rat) ↔ a < b := by
  constructor
  · intro h
    have hle : a ≤ b := intCast_rat_le_iff.mp (by grind)
    have hne : a ≠ b := fun heq => by rw [heq] at h; grind
    omega
  · intro h
    have hle : (a : Rat) ≤ (b : Rat) := intCast_rat_le_iff.mpr (by omega)
    have hne : (a : Rat) ≠ (b : Rat) := fun heq => by have := intCast_rat_eq_iff.mp heq; omega
    grind

theorem qpEq_iff {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    qpEq a b = true ↔ a.toRat = b.toRat := by
  unfold qpEq QPair.toRat
  have ha' : (0 : Rat) < (a.2 : Rat) := natCast_pos_rat ha
  have hb' : (0 : Rat) < (b.2 : Rat) := natCast_pos_rat hb
  simp only [beq_iff_eq]
  rw [← intCast_rat_eq_iff]
  have h1 : ((a.1 * (b.2 : Int) : Int) : Rat) = (a.1 : Rat) * (b.2 : Rat) := by
    have := intCast_natCast_rat b.2; grind
  have h2 : ((b.1 * (a.2 : Int) : Int) : Rat) = (b.1 : Rat) * (a.2 : Rat) := by
    have := intCast_natCast_rat a.2; grind
  rw [h1, h2]
  constructor
  · intro h
    have ha0 : (a.2 : Rat) ≠ 0 := by grind
    have hb0 : (b.2 : Rat) ≠ 0 := by grind
    grind
  · intro h
    have ha0 : (a.2 : Rat) ≠ 0 := by grind
    have hb0 : (b.2 : Rat) ≠ 0 := by grind
    grind

theorem qpLe_iff {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    qpLe a b = true ↔ a.toRat ≤ b.toRat := by
  unfold qpLe QPair.toRat
  have ha' : (0 : Rat) < (a.2 : Rat) := natCast_pos_rat ha
  have hb' : (0 : Rat) < (b.2 : Rat) := natCast_pos_rat hb
  simp only [decide_eq_true_eq]
  rw [← intCast_rat_le_iff]
  have h1 : ((a.1 * (b.2 : Int) : Int) : Rat) = (a.1 : Rat) * (b.2 : Rat) := by
    have := intCast_natCast_rat b.2; grind
  have h2 : ((b.1 * (a.2 : Int) : Int) : Rat) = (b.1 : Rat) * (a.2 : Rat) := by
    have := intCast_natCast_rat a.2; grind
  rw [h1, h2]
  have hab_pos : (0 : Rat) < (a.2 : Rat) * (b.2 : Rat) := Rat.mul_pos ha' hb'
  have hinv_pos : (0 : Rat) < 1 / ((a.2 : Rat) * (b.2 : Rat)) := by
    cases @Rat.le_total (1 / ((a.2 : Rat) * (b.2 : Rat))) 0 with
    | inl hle =>
      exfalso
      have hmul := Rat.mul_le_mul_of_nonneg_left hle (by grind : (0 : Rat) ≤ (a.2 : Rat) * (b.2 : Rat))
      have hne : (a.2 : Rat) * (b.2 : Rat) ≠ 0 := by grind
      grind
    | inr hge =>
      have hne : (1 / ((a.2 : Rat) * (b.2 : Rat))) ≠ 0 := by
        intro hz
        have hmul := congrArg (fun x => ((a.2 : Rat) * (b.2 : Rat)) * x) hz
        have hne' : (a.2 : Rat) * (b.2 : Rat) ≠ 0 := by grind
        grind
      grind
  constructor
  · intro h
    have hm := Rat.mul_le_mul_of_nonneg_left h (by grind : (0 : Rat) ≤ 1 / ((a.2 : Rat) * (b.2 : Rat)))
    have ha0 : (a.2 : Rat) ≠ 0 := by grind
    have hb0 : (b.2 : Rat) ≠ 0 := by grind
    grind
  · intro h
    have hm := Rat.mul_le_mul_of_nonneg_left h (by grind : (0 : Rat) ≤ (a.2 : Rat) * (b.2 : Rat))
    have ha0 : (a.2 : Rat) ≠ 0 := by grind
    have hb0 : (b.2 : Rat) ≠ 0 := by grind
    grind

theorem qpLt_iff {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    qpLt a b = true ↔ a.toRat < b.toRat := by
  have hle := qpLe_iff ha hb
  have heq := qpEq_iff ha hb
  unfold qpLe at hle
  unfold qpEq at heq
  unfold qpLt
  simp only [decide_eq_true_eq] at hle ⊢
  simp only [beq_iff_eq] at heq
  constructor
  · intro h
    have h1 : a.toRat ≤ b.toRat := hle.mp (by omega)
    have h2 : a.toRat ≠ b.toRat := fun eq => by have := heq.mpr eq; omega
    grind
  · intro h
    have h1 : a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int) := hle.mpr (by grind)
    have h2 : a.1 * (b.2 : Int) ≠ b.1 * (a.2 : Int) := fun eq => by have := heq.mp eq; grind
    omega

theorem qpAdd_toRat {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    (qpAdd a b).toRat = a.toRat + b.toRat := by
  unfold qpAdd QPair.toRat
  have ha' : (0 : Rat) < (a.2 : Rat) := natCast_pos_rat ha
  have hb' : (0 : Rat) < (b.2 : Rat) := natCast_pos_rat hb
  have hnum : ((a.1 * (b.2 : Int) + b.1 * (a.2 : Int) : Int) : Rat) =
      (a.1 : Rat) * (b.2 : Rat) + (b.1 : Rat) * (a.2 : Rat) := by
    have := intCast_natCast_rat a.2; have := intCast_natCast_rat b.2; grind
  have hden : ((a.2 * b.2 : Nat) : Rat) = (a.2 : Rat) * (b.2 : Rat) := by grind
  rw [hnum, hden]; grind

theorem qpSub_toRat {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    (qpSub a b).toRat = a.toRat - b.toRat := by
  unfold qpSub QPair.toRat
  have ha' : (0 : Rat) < (a.2 : Rat) := natCast_pos_rat ha
  have hb' : (0 : Rat) < (b.2 : Rat) := natCast_pos_rat hb
  have hnum : ((a.1 * (b.2 : Int) - b.1 * (a.2 : Int) : Int) : Rat) =
      (a.1 : Rat) * (b.2 : Rat) - (b.1 : Rat) * (a.2 : Rat) := by
    have := intCast_natCast_rat a.2; have := intCast_natCast_rat b.2; grind
  have hden : ((a.2 * b.2 : Nat) : Rat) = (a.2 : Rat) * (b.2 : Rat) := by grind
  rw [hnum, hden]; grind

theorem qpMul_toRat {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    (qpMul a b).toRat = a.toRat * b.toRat := by
  unfold qpMul QPair.toRat
  have ha' : (0 : Rat) < (a.2 : Rat) := natCast_pos_rat ha
  have hb' : (0 : Rat) < (b.2 : Rat) := natCast_pos_rat hb
  have hnum : ((a.1 * b.1 : Int) : Rat) = (a.1 : Rat) * (b.1 : Rat) := by grind
  have hden : ((a.2 * b.2 : Nat) : Rat) = (a.2 : Rat) * (b.2 : Rat) := by grind
  rw [hnum, hden]; grind

theorem qpMax_pos {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (qpMax a b).2 := by
  unfold qpMax; split <;> assumption

theorem qpMax_toRat {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    (qpMax a b).toRat = max a.toRat b.toRat := by
  unfold qpMax
  show (if qpLe a b = true then b else a).toRat = if a.toRat ≤ b.toRat then b.toRat else a.toRat
  by_cases h : qpLe a b = true
  · have hr := (qpLe_iff ha hb).mp h
    simp [h, hr]
  · have hr : ¬(a.toRat ≤ b.toRat) := fun hle => h ((qpLe_iff ha hb).mpr hle)
    simp [h, hr]

theorem qpNagumoF_pos {w : QPair} (hw : 0 < w.2) : 0 < (qpNagumoF w).2 := by
  unfold qpNagumoF
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hw) hw) hw

theorem qpNagumoF_toRat {w : QPair} (hw : 0 < w.2) :
    (qpNagumoF w).toRat = nagumoF w.toRat := by
  unfold qpNagumoF QPair.toRat nagumoF
  have hw' : (0 : Rat) < (w.2 : Rat) := natCast_pos_rat hw
  have hnum : ((w.1 * ((w.2 : Int) - w.1) * (10 * w.1 - 3 * (w.2 : Int)) : Int) : Rat) =
      (w.1 : Rat) * ((w.2 : Rat) - (w.1 : Rat)) * (10 * (w.1 : Rat) - 3 * (w.2 : Rat)) := by
    have := intCast_natCast_rat w.2; grind
  have hden : ((10 * w.2 * w.2 * w.2 : Nat) : Rat) =
      10 * (w.2 : Rat) * (w.2 : Rat) * (w.2 : Rat) := by grind
  rw [hnum, hden]; grind

theorem qpFMaxUB_pos {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (qpFMaxUB a b).2 := by
  unfold qpFMaxUB
  have hm := qpMax_pos (qpNagumoF_pos ha) (qpNagumoF_pos hb)
  split
  · exact qpMax_pos hm (by unfold fPeakUBPair; omega)
  · exact hm

theorem qpFMaxUB_toRat {a b : QPair} (ha : 0 < a.2) (hb : 0 < b.2) :
    (qpFMaxUB a b).toRat = fMaxUB a.toRat b.toRat := by
  unfold qpFMaxUB fMaxUB
  have hfa := qpNagumoF_pos ha
  have hfb := qpNagumoF_pos hb
  have hm_pos := qpMax_pos hfa hfb
  have hm_eq : (qpMax (qpNagumoF a) (qpNagumoF b)).toRat = max (nagumoF a.toRat) (nagumoF b.toRat) := by
    rw [qpMax_toRat hfa hfb, qpNagumoF_toRat ha, qpNagumoF_toRat hb]
  have hcond : (qpLt (729, 1000) b && qpLt a (730, 1000)) = true ↔
      (wPeakLo < b.toRat ∧ a.toRat < wPeakHi) := by
    rw [Bool.and_eq_true, qpLt_iff (by omega) hb, qpLt_iff ha (by omega)]
    unfold QPair.toRat wPeakLo wPeakHi; grind
  by_cases hc : (qpLt (729, 1000) b && qpLt a (730, 1000)) = true
  · have hrc := hcond.mp hc
    simp only [hc, ↓reduceIte, hrc, and_self]
    rw [qpMax_toRat hm_pos (by unfold fPeakUBPair; omega), hm_eq]
    have hp : fPeakUBPair.toRat = fPeakUB := fPeakUBPair_exact
    rw [hp]
  · have hrc : ¬(wPeakLo < b.toRat ∧ a.toRat < wPeakHi) := fun h => hc (hcond.mpr h)
    simp only [hc, Bool.false_eq_true, ↓reduceIte, hrc]
    exact hm_eq

theorem rawC2Lo_pos {r0sq : QPair} (hr : 0 < r0sq.2) : 0 < (rawC2Lo r0sq).2 :=
  Nat.mul_pos hr (by omega)

theorem rawC2Hi_pos {r0sq : QPair} (hr : 0 < r0sq.2) : 0 < (rawC2Hi r0sq).2 :=
  Nat.mul_pos hr (by omega)

theorem rawC2Lo_toRat {r0sq : QPair} (hr : 0 < r0sq.2) :
    (rawC2Lo r0sq).toRat = certC2Lo r0sq.toRat := by
  unfold rawC2Lo certC2Lo QPair.toRat piHiCompact
  have hr' : (0 : Rat) < (r0sq.2 : Rat) := natCast_pos_rat hr
  have hnum : ((4 * r0sq.1 * 10000000000000000 : Int) : Rat) =
      4 * (r0sq.1 : Rat) * 10000000000000000 := by grind
  have hden : ((r0sq.2 * (314159266 * 314159266) : Nat) : Rat) =
      (r0sq.2 : Rat) * (314159266 * 314159266) := by grind
  rw [hnum, hden]; grind

theorem rawC2Hi_toRat {r0sq : QPair} (hr : 0 < r0sq.2) :
    (rawC2Hi r0sq).toRat = certC2Hi r0sq.toRat := by
  unfold rawC2Hi certC2Hi QPair.toRat piLoCompact
  have hr' : (0 : Rat) < (r0sq.2 : Rat) := natCast_pos_rat hr
  have hnum : ((4 * r0sq.1 * 10000000000000000 : Int) : Rat) =
      4 * (r0sq.1 : Rat) * 10000000000000000 := by grind
  have hden : ((r0sq.2 * (314159265 * 314159265) : Nat) : Rat) =
      (r0sq.2 : Rat) * (314159265 * 314159265) := by grind
  rw [hnum, hden]; grind


/-! ## Part 2: Soundness of `expGridList` Against Any Abstract Exponential `E : Int → Rat` -/

/-- Specification of an abstract exponential `E(k) = exp(k / 50)` on `k : Int`. -/
structure Exp50Spec (E : Int → Rat) : Prop where
  zero     : E 0 = 1
  stepPos  : ∀ k : Int, E (k + 1) = E k * E 1
  stepNeg  : ∀ k : Int, E (k - 1) = E k * E (-1)
  posNonneg : (0 : Rat) ≤ E 1
  negNonneg : (0 : Rat) ≤ E (-1)
  posEncl  : ((e50LoN : Nat) : Rat) / (exp50Scale : Rat) ≤ E 1 ∧
             E 1 ≤ ((e50HiN : Nat) : Rat) / (exp50Scale : Rat)
  negEncl  : ((en50LoN : Nat) : Rat) / (exp50Scale : Rat) ≤ E (-1) ∧
             E (-1) ≤ ((en50HiN : Nat) : Rat) / (exp50Scale : Rat)

/-- Inductive predicate: every pair `(lo, hi)` in `grid` starting at index `k` encloses `E`. -/
def GridEncloses (E : Int → Rat) : Int → List (Nat × Nat) → Prop
  | _, [] => True
  | k, (lo, hi) :: rest =>
    ((lo : Nat) : Rat) / (exp50Scale : Rat) ≤ E k ∧
    E k ≤ ((hi : Nat) : Rat) / (exp50Scale : Rat) ∧
    GridEncloses E (k + 1) rest

private theorem gridEncloses_append {E : Int → Rat} {l1 l2 : List (Nat × Nat)} {k : Int}
    (h1 : GridEncloses E k l1) (h2 : GridEncloses E (k + l1.length) l2) :
    GridEncloses E k (l1 ++ l2) := by
  induction l1 generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil] at h2 ⊢
    have hk : k + (0 : Nat) = k := by omega
    rw [hk] at h2; exact h2
  | cons p rest ih =>
    rcases p with ⟨lo, hi⟩
    simp only [List.cons_append, GridEncloses] at h1 ⊢
    refine ⟨h1.1, h1.2.1, ih h1.2.2 ?_⟩
    simp only [List.length_cons] at h2
    have hk : k + 1 + (rest.length : Int) = k + ((rest.length + 1 : Nat) : Int) := by omega
    rw [hk]; exact h2

private theorem buildStepPairsRev_neg_encloses {E : Int → Rat} (hE : Exp50Spec E) :
    ∀ (n m : Nat) (acc : List (Nat × Nat)),
      GridEncloses E (-(m : Int)) acc →
      GridEncloses E (-(m + n : Int))
        (buildStepPairsRev en50LoN en50HiN n (stepLoN en50LoN m) (stepHiN en50HiN m) acc) := by
  have hneg := stepLoHi_sound (fun j => E (-(j : Int))) (E (-1)) en50LoN en50HiN
    (by simpa using hE.zero)
    (fun j => by
      have : -((j + 1 : Nat) : Int) = -(j : Int) - 1 := by omega
      rw [this, hE.stepNeg])
    hE.negNonneg hE.negEncl.1 hE.negEncl.2
  intro n
  induction n with
  | zero =>
    intro m acc hacc
    simp only [buildStepPairsRev]
    simpa using hacc
  | succ n ih =>
    intro m acc hacc
    simp only [buildStepPairsRev]
    have hstep := hneg (m + 1)
    have hacc' : GridEncloses E (-((m + 1 : Nat) : Int))
        ((stepLoN en50LoN (m + 1), stepHiN en50HiN (m + 1)) :: acc) := by
      simp only [GridEncloses]
      refine ⟨hstep.1, hstep.2, ?_⟩
      have : -((m + 1 : Nat) : Int) + 1 = -(m : Int) := by omega
      rw [this]; exact hacc
    have hres := ih (m + 1) ((stepLoN en50LoN (m + 1), stepHiN en50HiN (m + 1)) :: acc) hacc'
    have hk : -((m + 1 : Nat) + n : Int) = -(m + (n + 1) : Int) := by omega
    rw [hk] at hres
    exact hres

private theorem buildStepPairsRev_pos_encloses {E : Int → Rat} (hE : Exp50Spec E) :
    ∀ (n m : Nat) (acc : List (Nat × Nat)),
      (∀ (k : Int), k = (m : Int) - (acc.length : Int) + 1 → GridEncloses E k acc.reverse) →
      GridEncloses E ((m : Int) - (acc.length : Int) + 1)
        (buildStepPairsRev e50LoN e50HiN n (stepLoN e50LoN m) (stepHiN e50HiN m) acc).reverse := by
  have hpos := stepLoHi_sound (fun j => E (j : Int)) (E 1) e50LoN e50HiN
    (by simpa using hE.zero)
    (fun j => by
      have : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
      rw [this, hE.stepPos])
    hE.posNonneg hE.posEncl.1 hE.posEncl.2
  intro n
  induction n with
  | zero =>
    intro m acc hacc
    simp only [buildStepPairsRev]
    exact hacc _ rfl
  | succ n ih =>
    intro m acc hacc
    simp only [buildStepPairsRev]
    have hstep := hpos (m + 1)
    let p := (stepLoN e50LoN (m + 1), stepHiN e50HiN (m + 1))
    have hacc' : ∀ (k : Int), k = ((m + 1 : Nat) : Int) - ((p :: acc).length : Int) + 1 →
        GridEncloses E k (p :: acc).reverse := by
      intro k hk
      rw [List.reverse_cons]
      have hk_eq : k = (m : Int) - (acc.length : Int) + 1 := by
        simp only [List.length_cons] at hk; omega
      have h1 := hacc k hk_eq
      refine gridEncloses_append h1 ?_
      simp only [List.length_reverse, GridEncloses]
      have hk2 : k + (acc.length : Int) = ((m + 1 : Nat) : Int) := by omega
      rw [hk2]
      exact ⟨hstep.1, hstep.2, trivial⟩
    have hres := ih (m + 1) (p :: acc) hacc'
    have hlen : ((m + 1 : Nat) : Int) - ((p :: acc).length : Int) + 1 = (m : Int) - (acc.length : Int) + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen] at hres
    exact hres

private theorem buildStepPairsRev_length (sLo sHi : Nat) :
    ∀ (n cLo cHi : Nat) (acc : List (Nat × Nat)),
      (buildStepPairsRev sLo sHi n cLo cHi acc).length = acc.length + n := by
  intro n
  induction n with
  | zero => intro _ _ acc; simp [buildStepPairsRev]
  | succ n ih =>
    intro cLo cHi acc
    simp only [buildStepPairsRev]
    rw [ih]
    simp only [List.length_cons]; omega

/-- Main Lemma 2.1: `expGridList` strictly encloses `E(-350), E(-349), ..., E(250)`. -/
theorem expGridList_encloses {E : Int → Rat} (hE : Exp50Spec E) :
    GridEncloses E (-350) expGridList := by
  unfold expGridList
  have hneg : GridEncloses E (-350)
      (buildStepPairsRev en50LoN en50HiN 350 exp50Scale exp50Scale [(exp50Scale, exp50Scale)]) := by
    have h0 : GridEncloses E (-(0 : Int)) [(exp50Scale, exp50Scale)] := by
      simp only [GridEncloses, show -(0 : Int) = 0 from rfl, hE.zero]
      unfold exp50Scale; grind
    have h := buildStepPairsRev_neg_encloses hE 350 0 [(exp50Scale, exp50Scale)] h0
    simpa [stepLoN, stepHiN] using h
  have hpos : GridEncloses E 1
      (buildStepPairsRev e50LoN e50HiN 250 exp50Scale exp50Scale []).reverse := by
    have h0 : ∀ (k : Int), k = (0 : Int) - (([] : List (Nat × Nat)).length : Int) + 1 →
        GridEncloses E k ([] : List (Nat × Nat)).reverse := by
      intro _ _; simp [GridEncloses]
    have h := buildStepPairsRev_pos_encloses hE 250 0 [] h0
    simpa [stepLoN, stepHiN] using h
  refine gridEncloses_append hneg ?_
  rw [buildStepPairsRev_length]
  simp only [List.length_cons, List.length_nil]
  have hk : (-350 : Int) + ((1 + 350 : Nat) : Int) = 1 := by omega
  rw [hk]; exact hpos


/-! ## Part 3: Pointwise Supersolution Soundness of `checkRawSegWithGrid` -/

/-- Helper: if `checkRawSegWithGrid` returns `true`, all 7 rational pairs have positive denominators. -/
theorem checkRawSegWithGrid_pos_denoms {c2Lo c2Hi : QPair} {k : Int} {e0Lo e1Hi : Nat} {seg : RawSeg}
    (hok : checkRawSegWithGrid c2Lo c2Hi k e0Lo e1Hi seg = true) :
    0 < seg.s0.2 ∧ 0 < seg.s1.2 ∧ 0 < seg.w0.2 ∧ 0 < seg.w1.2 ∧
    0 < seg.wp0.2 ∧ 0 < seg.wp1.2 ∧ 0 < seg.c.2 := by
  unfold checkRawSegWithGrid at hok
  by_cases hden0 : (seg.s0.2 == 0 || seg.s1.2 == 0 || seg.w0.2 == 0 || seg.w1.2 == 0 ||
                    seg.wp0.2 == 0 || seg.wp1.2 == 0 || seg.c.2 == 0) = true
  · simp [hden0] at hok
  · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hden0
    rcases hden0 with ⟨⟨⟨⟨⟨⟨hs0d, hs1d⟩, hw0d⟩, hw1d⟩, hwp0d⟩, hwp1d⟩, hcd⟩
    exact ⟨Nat.pos_of_ne_zero hs0d, Nat.pos_of_ne_zero hs1d, Nat.pos_of_ne_zero hw0d,
           Nat.pos_of_ne_zero hw1d, Nat.pos_of_ne_zero hwp0d, Nat.pos_of_ne_zero hwp1d,
           Nat.pos_of_ne_zero hcd⟩

/-- Pointwise PDE supersolution soundness directly for a `RawSeg` verified by `checkRawSegWithGrid`. -/
theorem checkRawSegWithGrid_sound {r0sq : QPair} (hr0 : 0 < r0sq.2) (hr0_nn : 0 ≤ r0sq.1)
    {k : Int} {e0Lo e1Hi : Nat} {seg : RawSeg}
    (hok : checkRawSegWithGrid (rawC2Lo r0sq) (rawC2Hi r0sq) k e0Lo e1Hi seg = true) :
    let sp := seg.toSpline
    (sp.s0 < sp.s1) ∧
    (sp.s0 = (k : Rat) / 100) ∧
    (sp.w1 = sp.w0 + sp.wp0 * (sp.s1 - sp.s0) + sp.c * ((sp.s1 - sp.s0) * (sp.s1 - sp.s0)) / 2) ∧
    (sp.wp1 = sp.wp0 + sp.c * (sp.s1 - sp.s0)) ∧
    (sp.wp0 ≤ 0 ∧ sp.wp1 ≤ 0 ∧ (0 : Rat) ≤ sp.w1 ∧ sp.w0 ≤ 1) ∧
    (∀ {E0 E1 s J : Rat},
      ((e0Lo : Nat) : Rat) / (exp50Scale : Rat) ≤ E0 →
      E1 ≤ ((e1Hi : Nat) : Rat) / (exp50Scale : Rat) →
      sp.s0 ≤ s → s ≤ sp.s1 →
      (0 : Rat) ≤ J →
      ((0 : Rat) < sp.s0 → certC2Lo r0sq.toRat * (E0 - 1) ≤ J) →
      (J ≤ certC2Hi r0sq.toRat * (E1 + 1)) →
      (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  unfold checkRawSegWithGrid at hok
  by_cases hden0 : (seg.s0.2 == 0 || seg.s1.2 == 0 || seg.w0.2 == 0 || seg.w1.2 == 0 ||
                    seg.wp0.2 == 0 || seg.wp1.2 == 0 || seg.c.2 == 0) = true
  · simp [hden0] at hok
  · have hden0_f : (seg.s0.2 == 0 || seg.s1.2 == 0 || seg.w0.2 == 0 || seg.w1.2 == 0 ||
                    seg.wp0.2 == 0 || seg.wp1.2 == 0 || seg.c.2 == 0) = false :=
      Bool.eq_false_iff.mpr hden0
    simp only [hden0_f, Bool.false_eq_true, ↓reduceIte] at hok
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hden0
    rcases hden0 with ⟨⟨⟨⟨⟨⟨hs0d, hs1d⟩, hw0d⟩, hw1d⟩, hwp0d⟩, hwp1d⟩, hcd⟩
    have hs0_pos : 0 < seg.s0.2 := Nat.pos_of_ne_zero hs0d
    have hs1_pos : 0 < seg.s1.2 := Nat.pos_of_ne_zero hs1d
    have hw0_pos : 0 < seg.w0.2 := Nat.pos_of_ne_zero hw0d
    have hw1_pos : 0 < seg.w1.2 := Nat.pos_of_ne_zero hw1d
    have hwp0_pos : 0 < seg.wp0.2 := Nat.pos_of_ne_zero hwp0d
    have hwp1_pos : 0 < seg.wp1.2 := Nat.pos_of_ne_zero hwp1d
    have hc_pos : 0 < seg.c.2 := Nat.pos_of_ne_zero hcd
    let ds := qpSub seg.s1 seg.s0
    have hds_pos : 0 < ds.2 := Nat.mul_pos hs1_pos hs0_pos
    let rhsW1 := qpAdd (qpAdd seg.w0 (qpMul seg.wp0 ds))
                       (qpMul seg.c (ds.1 * ds.1, 2 * ds.2 * ds.2))
    let rhsWp1 := qpAdd seg.wp0 (qpMul seg.c ds)
    have hgeom : (decide (0 < ds.1) && qpEq seg.s0 (k, 100) && qpEq seg.w1 rhsW1 &&
        qpEq seg.wp1 rhsWp1 && decide (seg.wp0.1 ≤ 0) && decide (seg.wp1.1 ≤ 0) &&
        decide (0 ≤ seg.w1.1) && qpLe seg.w0 (1, 1)) = true := by
      cases h : (decide (0 < (qpSub seg.s1 seg.s0).1) && qpEq seg.s0 (k, 100) &&
          qpEq seg.w1 (qpAdd (qpAdd seg.w0 (qpMul seg.wp0 (qpSub seg.s1 seg.s0)))
            (qpMul seg.c ((qpSub seg.s1 seg.s0).1 * (qpSub seg.s1 seg.s0).1,
              2 * (qpSub seg.s1 seg.s0).2 * (qpSub seg.s1 seg.s0).2))) &&
          qpEq seg.wp1 (qpAdd seg.wp0 (qpMul seg.c (qpSub seg.s1 seg.s0))) &&
          decide (seg.wp0.1 ≤ 0) && decide (seg.wp1.1 ≤ 0) &&
          decide (0 ≤ seg.w1.1) && qpLe seg.w0 (1, 1))
      · simp only [h, Bool.not_false, ↓reduceIte] at hok
        exact absurd hok Bool.false_ne_true
      · rfl
    · have hgeom_exp : (decide (0 < (qpSub seg.s1 seg.s0).1) && qpEq seg.s0 (k, 100) &&
          qpEq seg.w1 (qpAdd (qpAdd seg.w0 (qpMul seg.wp0 (qpSub seg.s1 seg.s0)))
            (qpMul seg.c ((qpSub seg.s1 seg.s0).1 * (qpSub seg.s1 seg.s0).1,
              2 * (qpSub seg.s1 seg.s0).2 * (qpSub seg.s1 seg.s0).2))) &&
          qpEq seg.wp1 (qpAdd seg.wp0 (qpMul seg.c (qpSub seg.s1 seg.s0))) &&
          decide (seg.wp0.1 ≤ 0) && decide (seg.wp1.1 ≤ 0) &&
          decide (0 ≤ seg.w1.1) && qpLe seg.w0 (1, 1)) = true := hgeom
      simp only [hgeom_exp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgeom
      rcases hgeom with ⟨⟨⟨⟨⟨⟨⟨hds_gt0, hs0_k⟩, hw1_eq⟩, hwp1_eq⟩, hwp0_le⟩, hwp1_le⟩, hw1_nn⟩, hw0_le1⟩
      -- Lift geometric facts to Rat
      have hds_rat : ds.toRat = seg.s1.toRat - seg.s0.toRat := qpSub_toRat hs1_pos hs0_pos
      have hds_lt : seg.s0.toRat < seg.s1.toRat := by
        have hpos : (0 : Rat) < ds.toRat := by
          unfold QPair.toRat
          have h1 : (0 : Rat) < (ds.1 : Rat) := intCast_rat_lt_iff.mpr hds_gt0
          have h2 : (0 : Rat) < (ds.2 : Rat) := natCast_pos_rat hds_pos
          have hinv : (0 : Rat) < 1 / (ds.2 : Rat) := by
            cases @Rat.le_total (1 / (ds.2 : Rat)) 0 with
            | inl hle =>
              exfalso
              have hm := Rat.mul_le_mul_of_nonneg_left hle (by grind : (0 : Rat) ≤ (ds.2 : Rat))
              have hne : (ds.2 : Rat) ≠ 0 := by grind
              grind
            | inr hge =>
              have hne : (1 / (ds.2 : Rat)) ≠ 0 := fun hz => by
                have hm := congrArg (fun x => (ds.2 : Rat) * x) hz
                have hne' : (ds.2 : Rat) ≠ 0 := by grind
                grind
              grind
          have hm := Rat.mul_pos h1 hinv
          grind
        grind
      have hs0_eq : seg.s0.toRat = (k : Rat) / 100 := by
        have := (qpEq_iff hs0_pos (by omega)).mp hs0_k
        rw [this]; unfold QPair.toRat; grind
      have hsq_pos : 0 < 2 * ds.2 * ds.2 := Nat.mul_pos (Nat.mul_pos (by omega) hds_pos) hds_pos
      have hrhsW1_pos : 0 < rhsW1.2 :=
        Nat.mul_pos (Nat.mul_pos hw0_pos (Nat.mul_pos hwp0_pos hds_pos)) (Nat.mul_pos hc_pos hsq_pos)
      have hw1_rat : seg.w1.toRat =
          seg.w0.toRat + seg.wp0.toRat * (seg.s1.toRat - seg.s0.toRat) +
          seg.c.toRat * ((seg.s1.toRat - seg.s0.toRat) * (seg.s1.toRat - seg.s0.toRat)) / 2 := by
        have h := (qpEq_iff hw1_pos hrhsW1_pos).mp hw1_eq
        rw [h]
        change (qpAdd (qpAdd seg.w0 (qpMul seg.wp0 ds))
                      (qpMul seg.c (ds.1 * ds.1, 2 * ds.2 * ds.2))).toRat = _
        rw [qpAdd_toRat (Nat.mul_pos hw0_pos (Nat.mul_pos hwp0_pos hds_pos)) (Nat.mul_pos hc_pos hsq_pos),
            qpAdd_toRat hw0_pos (Nat.mul_pos hwp0_pos hds_pos),
            qpMul_toRat hwp0_pos hds_pos,
            qpMul_toRat hc_pos hsq_pos,
            hds_rat]
        have hsq_eq : QPair.toRat (ds.1 * ds.1, 2 * ds.2 * ds.2) =
            ((seg.s1.toRat - seg.s0.toRat) * (seg.s1.toRat - seg.s0.toRat)) / 2 := by
          rw [← hds_rat]
          unfold QPair.toRat
          have h1 : ((ds.1 * ds.1 : Int) : Rat) = (ds.1 : Rat) * (ds.1 : Rat) := by grind
          have h2 : ((2 * ds.2 * ds.2 : Nat) : Rat) = 2 * (ds.2 : Rat) * (ds.2 : Rat) := by grind
          have hd0 : (ds.2 : Rat) ≠ 0 := by have := natCast_pos_rat hds_pos; grind
          rw [h1, h2]; grind
        rw [hsq_eq]; grind
      have hrhsWp1_pos : 0 < rhsWp1.2 := Nat.mul_pos hwp0_pos (Nat.mul_pos hc_pos hds_pos)
      have hwp1_rat : seg.wp1.toRat = seg.wp0.toRat + seg.c.toRat * (seg.s1.toRat - seg.s0.toRat) := by
        have h := (qpEq_iff hwp1_pos hrhsWp1_pos).mp hwp1_eq
        rw [h]
        change (qpAdd seg.wp0 (qpMul seg.c ds)).toRat = _
        rw [qpAdd_toRat hwp0_pos (Nat.mul_pos hc_pos hds_pos), qpMul_toRat hc_pos hds_pos, hds_rat]
      have hwp0_rat : seg.wp0.toRat ≤ 0 := by
        have h : qpLe seg.wp0 (0, 1) = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
        have := (qpLe_iff hwp0_pos (by omega)).mp h
        have hz : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
        grind
      have hwp1_rat_le : seg.wp1.toRat ≤ 0 := by
        have h : qpLe seg.wp1 (0, 1) = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
        have := (qpLe_iff hwp1_pos (by omega)).mp h
        have hz : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
        grind
      have hw1_rat_nn : (0 : Rat) ≤ seg.w1.toRat := by
        have h : qpLe (0, 1) seg.w1 = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
        have := (qpLe_iff (by omega) hw1_pos).mp h
        have hz : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
        grind
      have hw0_rat_le1 : seg.w0.toRat ≤ 1 := by
        have := (qpLe_iff hw0_pos (by omega)).mp hw0_le1
        have ho : QPair.toRat (1, 1) = 1 := by unfold QPair.toRat; grind
        grind
      refine ⟨hds_lt, hs0_eq, hw1_rat, hwp1_rat, ⟨hwp0_rat, hwp1_rat_le, hw1_rat_nn, hw0_rat_le1⟩, ?_⟩
      intro E0 E1 s J hE0 hE1 hs0 hs1 hJ0 hJ_lo hJ_hi
      have heval0 : seg.toSpline.eval seg.s0.toRat = seg.w0.toRat := by
        unfold RawSeg.toSpline SplineSegment.eval; grind
      have heval1 : seg.toSpline.eval seg.s1.toRat = seg.w1.toRat := by
        unfold RawSeg.toSpline SplineSegment.eval; rw [hw1_rat]
      have hlo_w : seg.w1.toRat ≤ seg.toSpline.eval s := by
        rw [← heval1]
        exact seg.toSpline.eval_antitone hds_lt hwp1_rat hwp0_rat hwp1_rat_le hs0 hs1 Rat.le_refl
      have hhi_w : seg.toSpline.eval s ≤ seg.w0.toRat := by
        rw [← heval0]
        exact seg.toSpline.eval_antitone hds_lt hwp1_rat hwp0_rat hwp1_rat_le Rat.le_refl hs0 hs1
      have hf_le : nagumoF (seg.toSpline.eval s) ≤ fMaxUB seg.w1.toRat seg.w0.toRat :=
        f_le_fMaxUB hw1_rat_nn hlo_w hhi_w hw0_rat_le1
      refine ⟨by grind, by grind, ?_⟩
      let fHi := qpFMaxUB seg.w1 seg.w0
      have hfHi_pos : 0 < fHi.2 := qpFMaxUB_pos hw1_pos hw0_pos
      have hfHi_rat : fHi.toRat = fMaxUB seg.w1.toRat seg.w0.toRat := qpFMaxUB_toRat hw1_pos hw0_pos
      have hc2Lo_pos := rawC2Lo_pos hr0
      have hc2Hi_pos := rawC2Hi_pos hr0
      have h0_rat : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
      have h1_rat : QPair.toRat (1, 1) = 1 := by unfold QPair.toRat; grind
      have hr0_rat_nn : (0 : Rat) ≤ r0sq.toRat := by
        have h : qpLe (0, 1) r0sq = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
        have := (qpLe_iff (by omega) hr0).mp h
        grind
      by_cases hfpos : 0 ≤ fHi.1
      · simp only [fHi, hfpos, decide_true, ↓reduceIte] at hok
        cases hs1k : qpEq seg.s1 (k + 1, 100)
        · simp [hs1k] at hok
        · simp only [hs1k, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
          have he1_pos : 0 < exp50Scale := by unfold exp50Scale; omega
          let e2Hi : QPair := ((e1Hi : Int), exp50Scale)
          let term := qpMul (qpMul (rawC2Hi r0sq) (qpAdd e2Hi (1, 1))) fHi
          have hterm_pos : 0 < term.2 :=
            Nat.mul_pos (Nat.mul_pos hc2Hi_pos (Nat.mul_pos he1_pos (by omega))) hfHi_pos
          have hlt := (qpLt_iff (Nat.mul_pos hc_pos hterm_pos) (by omega)).mp hok
          rw [qpAdd_toRat hc_pos hterm_pos,
              qpMul_toRat (Nat.mul_pos hc2Hi_pos (Nat.mul_pos he1_pos (by omega))) hfHi_pos,
              qpMul_toRat hc2Hi_pos (Nat.mul_pos he1_pos (by omega)),
              qpAdd_toRat he1_pos (by omega),
              rawC2Hi_toRat hr0, hfHi_rat, h0_rat, h1_rat] at hlt
          have hf_nn : (0 : Rat) ≤ fMaxUB seg.w1.toRat seg.w0.toRat := by
            rw [← hfHi_rat]
            have h : qpLe (0, 1) fHi = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
            have := (qpLe_iff (by omega) hfHi_pos).mp h
            grind
          have hc2Hi_nn : (0 : Rat) ≤ certC2Hi r0sq.toRat := by
            rw [← rawC2Hi_toRat hr0]
            have h : qpLe (0, 1) (rawC2Hi r0sq) = true := by
              unfold qpLe rawC2Hi; simp only [decide_eq_true_eq]; omega
            have := (qpLe_iff (by omega) hc2Hi_pos).mp h
            grind
          have he2Hi_eq : e2Hi.toRat = ((e1Hi : Nat) : Rat) / (exp50Scale : Rat) := by
            unfold QPair.toRat; simp only [e2Hi, intCast_natCast_rat]
          have hJ_ub : J ≤ certC2Hi r0sq.toRat * (e2Hi.toRat + 1) := by
            have hE1' : E1 + 1 ≤ e2Hi.toRat + 1 := by rw [he2Hi_eq]; grind
            have hm := Rat.mul_le_mul_of_nonneg_left hE1' hc2Hi_nn
            grind
          have h1 : J * nagumoF (seg.toSpline.eval s) ≤ J * fMaxUB seg.w1.toRat seg.w0.toRat :=
            Rat.mul_le_mul_of_nonneg_left hf_le hJ0
          have h2 : J * fMaxUB seg.w1.toRat seg.w0.toRat ≤
              certC2Hi r0sq.toRat * (e2Hi.toRat + 1) * fMaxUB seg.w1.toRat seg.w0.toRat :=
            Rat.mul_le_mul_of_nonneg_right hJ_ub hf_nn
          change seg.c.toRat + J * nagumoF (seg.toSpline.eval s) < 0
          grind
      · simp only [fHi, hfpos, decide_false, Bool.false_eq_true, ↓reduceIte] at hok
        let e2Lo : QPair := ((e0Lo : Int), exp50Scale)
        cases hk_gt0 : decide (0 < k)
        · simp [hk_gt0] at hok
        · cases he2_gt1 : qpLt (1, 1) ((e0Lo : Int), exp50Scale)
          · simp [hk_gt0, he2_gt1] at hok
          · simp only [hk_gt0, he2_gt1, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hok
            have hk_pos : 0 < k := by simpa [decide_eq_true_eq] using hk_gt0
            have he0_pos : 0 < exp50Scale := by unfold exp50Scale; omega
            let term := qpMul (qpMul (rawC2Lo r0sq) (qpSub e2Lo (1, 1))) fHi
            have hterm_pos : 0 < term.2 :=
              Nat.mul_pos (Nat.mul_pos hc2Lo_pos (Nat.mul_pos he0_pos (by omega))) hfHi_pos
            have hlt := (qpLt_iff (Nat.mul_pos hc_pos hterm_pos) (by omega)).mp hok
            rw [qpAdd_toRat hc_pos hterm_pos,
                qpMul_toRat (Nat.mul_pos hc2Lo_pos (Nat.mul_pos he0_pos (by omega))) hfHi_pos,
                qpMul_toRat hc2Lo_pos (Nat.mul_pos he0_pos (by omega)),
                qpSub_toRat he0_pos (by omega),
                rawC2Lo_toRat hr0, hfHi_rat, h0_rat, h1_rat] at hlt
            have hs0_pos_rat : (0 : Rat) < seg.s0.toRat := by
              rw [hs0_eq]
              have hk' : (0 : Rat) < (k : Rat) := intCast_rat_lt_iff.mpr hk_pos
              grind
            have hJ_lb0 : certC2Lo r0sq.toRat * (E0 - 1) ≤ J := hJ_lo hs0_pos_rat
            have hc2Lo_nn : (0 : Rat) ≤ certC2Lo r0sq.toRat := by
              rw [← rawC2Lo_toRat hr0]
              have h : qpLe (0, 1) (rawC2Lo r0sq) = true := by
                unfold qpLe rawC2Lo; simp only [decide_eq_true_eq]; omega
              have := (qpLe_iff (by omega) hc2Lo_pos).mp h
              grind
            have he2Lo_eq : e2Lo.toRat = ((e0Lo : Nat) : Rat) / (exp50Scale : Rat) := by
              unfold QPair.toRat; simp only [e2Lo, intCast_natCast_rat]
            have hJ_lb : certC2Lo r0sq.toRat * (e2Lo.toRat - 1) ≤ J := by
              have hE0' : e2Lo.toRat - 1 ≤ E0 - 1 := by rw [he2Lo_eq]; grind
              have hm := Rat.mul_le_mul_of_nonneg_left hE0' hc2Lo_nn
              grind
            have hf_le0 : fMaxUB seg.w1.toRat seg.w0.toRat ≤ 0 := by
              rw [← hfHi_rat]
              have h : qpLe fHi (0, 1) = true := by unfold qpLe; simp only [decide_eq_true_eq]; omega
              have := (qpLe_iff hfHi_pos (by omega)).mp h
              grind
            have h1 : J * nagumoF (seg.toSpline.eval s) ≤ J * fMaxUB seg.w1.toRat seg.w0.toRat :=
              Rat.mul_le_mul_of_nonneg_left hf_le hJ0
            have hneg_nn : (0 : Rat) ≤ -(fMaxUB seg.w1.toRat seg.w0.toRat) := by grind
            have h2' := Rat.mul_le_mul_of_nonneg_right hJ_lb hneg_nn
            have h2 : J * fMaxUB seg.w1.toRat seg.w0.toRat ≤
                certC2Lo r0sq.toRat * (e2Lo.toRat - 1) * fMaxUB seg.w1.toRat seg.w0.toRat := by
              grind
            change seg.c.toRat + J * nagumoF (seg.toSpline.eval s) < 0
            grind


/-! ## Part 4: Full-Certificate Soundness Bridge (`checkFullRawCert` → Exact `Rat` Theorems) -/

/-- Helper: in a chained strictly-increasing segment list, every segment starts at or after the head. -/
private theorem chain_head_le_mem :
    ∀ (segs : List SplineSegment),
      checkChain segs = true →
      (∀ seg ∈ segs, seg.s0 < seg.s1) →
      ∀ (hd : SplineSegment) (tl : List SplineSegment),
        segs = hd :: tl →
        ∀ seg ∈ segs, hd.s0 ≤ seg.s0 := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _ h; cases h
  | cons a rest ih =>
    intro hchain hlt hd tl heq seg hmem
    injection heq with ha htl
    subst ha; subst htl
    cases hmem with
    | head => grind
    | tail _ hmem_rest =>
      cases rest with
      | nil => cases hmem_rest
      | cons b rest' =>
        simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at hchain
        rcases hchain with ⟨⟨⟨hs1_eq, _⟩, _⟩, hchain_rest⟩
        have ha_lt := hlt a List.mem_cons_self
        have hlt_rest : ∀ s' ∈ b :: rest', s'.s0 < s'.s1 :=
          fun s' hm => hlt s' (List.mem_cons_of_mem a hm)
        have hb_le := ih hchain_rest hlt_rest b rest' rfl seg hmem_rest
        grind

/-- Helper: evaluating a valid chained spline at any knot `seg.s0` returns `seg.w0`. -/
theorem evalSegments_at_knot :
    ∀ (segs : List SplineSegment) (tailW : Rat),
      checkChain segs = true →
      (∀ seg ∈ segs, seg.s0 < seg.s1 ∧
        seg.w1 = seg.w0 + seg.wp0 * (seg.s1 - seg.s0) + seg.c * ((seg.s1 - seg.s0) * (seg.s1 - seg.s0)) / 2) →
      ∀ seg ∈ segs, evalSegments segs tailW seg.s0 = seg.w0 := by
  intro segs tailW
  induction segs with
  | nil => intro _ _ _ h; cases h
  | cons hd tl ih =>
    intro hchain hall seg hmem
    have hhd := hall hd List.mem_cons_self
    cases hmem with
    | head =>
      simp only [evalSegments]
      have hle : hd.s0 ≤ hd.s1 := by grind
      simp only [hle, ↓reduceIte]
      unfold SplineSegment.eval; grind
    | tail _ hmem_tl =>
      cases tl with
      | nil => cases hmem_tl
      | cons nxt tl' =>
        simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at hchain
        rcases hchain with ⟨⟨⟨hs1_eq, hw1_eq⟩, _⟩, hchain_tl⟩
        have hall_tl : ∀ s' ∈ nxt :: tl', s'.s0 < s'.s1 ∧
            s'.w1 = s'.w0 + s'.wp0 * (s'.s1 - s'.s0) + s'.c * ((s'.s1 - s'.s0) * (s'.s1 - s'.s0)) / 2 :=
          fun s' hm => hall s' (List.mem_cons_of_mem hd hm)
        cases hmem_tl with
        | head =>
          simp only [evalSegments]
          have hle : seg.s0 ≤ hd.s1 := by grind
          simp only [hle, ↓reduceIte]
          rw [← hs1_eq]
          unfold SplineSegment.eval
          grind
        | tail _ hmem_tl' =>
          have hnxt := hall_tl nxt List.mem_cons_self
          have hlt_tl : ∀ s' ∈ nxt :: tl', s'.s0 < s'.s1 := fun s' hm => (hall_tl s' hm).1
          cases tl' with
          | nil => cases hmem_tl'
          | cons nxt2 tl'' =>
            have hchain_tl_copy := hchain_tl
            simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at hchain_tl_copy
            rcases hchain_tl_copy with ⟨⟨⟨hs1_eq2, _⟩, _⟩, hchain_tl2⟩
            have hlt_tl2 : ∀ s' ∈ nxt2 :: tl'', s'.s0 < s'.s1 :=
              fun s' hm => hlt_tl s' (List.mem_cons_of_mem nxt hm)
            have hge := chain_head_le_mem (nxt2 :: tl'') hchain_tl2 hlt_tl2 nxt2 tl'' rfl seg hmem_tl'
            have hnotle : ¬(seg.s0 ≤ hd.s1) := by grind
            simp only [evalSegments, hnotle, ↓reduceIte]
            exact ih hchain_tl hall_tl seg (List.mem_cons_of_mem nxt hmem_tl')

/-- Helper: if `checkSegsLoop` succeeds on `hd :: tl`, then `hd` has all positive denominators. -/
private theorem checkSegsLoop_head_pos_denoms {c2Lo c2Hi uMouth uS0 : QPair}
    {k : Int} {grid : List (Nat × Nat)} {hd : RawSeg} {tl : List RawSeg} {mIn zIn : Bool}
    (hok : checkSegsLoop c2Lo c2Hi uMouth uS0 k grid (hd :: tl) mIn zIn = true) :
    0 < hd.s0.2 ∧ 0 < hd.s1.2 ∧ 0 < hd.w0.2 ∧ 0 < hd.w1.2 ∧
    0 < hd.wp0.2 ∧ 0 < hd.wp1.2 ∧ 0 < hd.c.2 := by
  cases tl with
  | nil =>
    cases grid with
    | nil => simp [checkSegsLoop] at hok
    | cons g0 gRest =>
      cases gRest with
      | nil => simp [checkSegsLoop] at hok
      | cons g1 gRest' =>
        simp only [checkSegsLoop, Bool.and_eq_true] at hok
        exact checkRawSegWithGrid_pos_denoms hok.1.1.1.1
  | cons nxt rest =>
    cases grid with
    | nil => simp [checkSegsLoop] at hok
    | cons g0 gRest =>
      cases gRest with
      | nil => simp [checkSegsLoop] at hok
      | cons g1 gRest' =>
        simp only [checkSegsLoop] at hok
        by_cases h1 : (checkRawSegWithGrid c2Lo c2Hi k g0.1 g1.2 hd &&
            (qpEq hd.s1 nxt.s0 && qpEq hd.w1 nxt.w0 && qpEq hd.wp1 nxt.wp0)) = true
        · simp only [Bool.and_eq_true] at h1
          exact checkRawSegWithGrid_pos_denoms h1.1
        · simp [h1] at hok

/-- Inductive soundness of `checkSegsLoop` over any non-empty segment list. -/
theorem checkSegsLoop_sound {r0sq uMouth uS0 : QPair}
    (hr0 : 0 < r0sq.2) (hr0_nn : 0 ≤ r0sq.1)
    (huM : 0 < uMouth.2) (huZ : 0 < uS0.2)
    {E : Int → Rat} :
    ∀ (segs : List RawSeg) (k : Int) (grid : List (Nat × Nat)) (mIn zIn : Bool),
      segs ≠ [] →
      GridEncloses E k grid →
      checkSegsLoop (rawC2Lo r0sq) (rawC2Hi r0sq) uMouth uS0 k grid segs mIn zIn = true →
      checkChain (segs.map RawSeg.toSpline) = true ∧
      (∀ seg ∈ segs,
        let sp := seg.toSpline
        sp.s0 < sp.s1 ∧
        sp.w1 = sp.w0 + sp.wp0 * (sp.s1 - sp.s0) + sp.c * ((sp.s1 - sp.s0) * (sp.s1 - sp.s0)) / 2 ∧
        sp.wp1 = sp.wp0 + sp.c * (sp.s1 - sp.s0) ∧
        sp.wp0 ≤ 0 ∧ sp.wp1 ≤ 0 ∧ (0 : Rat) ≤ sp.w1 ∧ sp.w0 ≤ 1 ∧
        ∃ ki : Int,
          sp.s0 = (ki : Rat) / 100 ∧
          ∀ {s J : Rat},
            sp.s0 ≤ s → s ≤ sp.s1 →
            (0 : Rat) ≤ J →
            ((0 : Rat) < sp.s0 → certC2Lo r0sq.toRat * (E ki - 1) ≤ J) →
            (J ≤ certC2Hi r0sq.toRat * (E (ki + 1) + 1)) →
            (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) ∧
      (∃ last, segs.getLast? = some last ∧
        (0 : Rat) < last.w1.toRat ∧ last.w1.toRat < 3 / 10 ∧
        last.wp1.toRat = 0 ∧ nagumoF last.w1.toRat < 0) ∧
      (mIn = true ∨ ∃ seg ∈ segs, seg.s0.toRat = -42 / 100 ∧ seg.w0.toRat ≤ uMouth.toRat) ∧
      (zIn = true ∨ ∃ seg ∈ segs, seg.s0.toRat = 0 ∧ seg.w0.toRat ≤ uS0.toRat) := by
  intro segs
  induction segs with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons seg rest ih =>
    intro k grid mIn zIn _ hgrid hok
    cases rest with
    | nil =>
      cases grid with
      | nil => simp [checkSegsLoop] at hok
      | cons g0 gRest =>
        cases gRest with
        | nil => simp [checkSegsLoop] at hok
        | cons g1 gRest' =>
          rcases g0 with ⟨e0Lo, e0Hi⟩
          rcases g1 with ⟨e1Lo, e1Hi⟩
          simp only [checkSegsLoop, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
                     beq_iff_eq] at hok
          rcases hok with ⟨⟨⟨⟨hsegOk, ⟨⟨hlw1_gt0, hlw1_lt3⟩, hlwp1_0⟩⟩, hmOk⟩, hzOk⟩, _he1⟩
          simp only [GridEncloses] at hgrid
          rcases hgrid with ⟨he0Lo, _, _, he1Hi, _⟩
          have hden := checkRawSegWithGrid_pos_denoms hsegOk
          have hsound := checkRawSegWithGrid_sound hr0 hr0_nn hsegOk
          rcases hsound with ⟨hds, hs0_k, hw1_eq, hwp1_eq, ⟨hwp0_le, hwp1_le, hw1_nn, hw0_le1⟩, hsup⟩
          have hlw1_pos : (0 : Rat) < seg.w1.toRat := by
            have h : qpLt (0, 1) seg.w1 = true := by unfold qpLt; simp only [decide_eq_true_eq]; omega
            have := (qpLt_iff (by omega) hden.2.2.2.1).mp h
            have hz : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
            grind
          have hlw1_lt3_rat : seg.w1.toRat < 3 / 10 := by
            have := (qpLt_iff hden.2.2.2.1 (by omega)).mp hlw1_lt3
            have h3 : QPair.toRat (3, 10) = 3 / 10 := by unfold QPair.toRat; grind
            grind
          have hlwp1_rat : seg.wp1.toRat = 0 := by
            unfold QPair.toRat; rw [hlwp1_0]; grind
          refine ⟨by simp [checkChain], ?_, ⟨seg, rfl, hlw1_pos, hlw1_lt3_rat, hlwp1_rat, f_tail_neg hlw1_pos hlw1_lt3_rat⟩, ?_, ?_⟩
          · intro s' hm
            cases hm with
            | head =>
              exact ⟨hds, hw1_eq, hwp1_eq, hwp0_le, hwp1_le, hw1_nn, hw0_le1, k, hs0_k,
                     fun hs0 hs1 hJ0 hJlo hJhi => hsup he0Lo he1Hi hs0 hs1 hJ0 hJlo hJhi⟩
            | tail _ h => cases h
          · cases hmOk with
            | inl hm => exact Or.inl hm
            | inr hm =>
              rcases hm with ⟨hk_eq, hle⟩
              refine Or.inr ⟨seg, List.mem_cons_self, ?_, (qpLe_iff hden.2.2.1 huM).mp hle⟩
              change seg.toSpline.s0 = -42 / 100; rw [hs0_k, hk_eq]; grind
          · cases hzOk with
            | inl hz => exact Or.inl hz
            | inr hz =>
              rcases hz with ⟨hk_eq, hle⟩
              refine Or.inr ⟨seg, List.mem_cons_self, ?_, (qpLe_iff hden.2.2.1 huZ).mp hle⟩
              change seg.toSpline.s0 = 0; rw [hs0_k, hk_eq]; grind
    | cons nxt rest' =>
      cases grid with
      | nil => simp [checkSegsLoop] at hok
      | cons g0 gRest =>
        cases gRest with
        | nil => simp [checkSegsLoop] at hok
        | cons g1 gRest' =>
          rcases g0 with ⟨e0Lo, e0Hi⟩
          rcases g1 with ⟨e1Lo, e1Hi⟩
          simp only [checkSegsLoop] at hok
          by_cases hstep : (checkRawSegWithGrid (rawC2Lo r0sq) (rawC2Hi r0sq) k e0Lo e1Hi seg &&
              (qpEq seg.s1 nxt.s0 && qpEq seg.w1 nxt.w0 && qpEq seg.wp1 nxt.wp0)) = true
          · simp only [hstep, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
            simp only [Bool.and_eq_true] at hstep
            rcases hstep with ⟨hsegOk, ⟨⟨hcs, hcw⟩, hcwp⟩⟩
            simp only [GridEncloses] at hgrid
            rcases hgrid with ⟨he0Lo, _, hgrid_rest⟩
            have he1Hi : E (k + 1) ≤ ((e1Hi : Nat) : Rat) / (exp50Scale : Rat) := hgrid_rest.2.1
            have hden := checkRawSegWithGrid_pos_denoms hsegOk
            have hden_nxt := checkSegsLoop_head_pos_denoms hok
            have hsound := checkRawSegWithGrid_sound hr0 hr0_nn hsegOk
            rcases hsound with ⟨hds, hs0_k, hw1_eq, hwp1_eq, ⟨hwp0_le, hwp1_le, hw1_nn, hw0_le1⟩, hsup⟩
            have hih := ih (k + 1) ((e1Lo, e1Hi) :: gRest')
              (mIn || (k == -42 && qpLe seg.w0 uMouth))
              (zIn || (k == 0 && qpLe seg.w0 uS0))
              (List.cons_ne_nil nxt rest') hgrid_rest hok
            rcases hih with ⟨hchain_rest, hall_rest, hlast_rest, hm_rest, hz_rest⟩
            have hcs_rat : seg.s1.toRat = nxt.s0.toRat := (qpEq_iff hden.2.1 hden_nxt.1).mp hcs
            have hcw_rat : seg.w1.toRat = nxt.w0.toRat := (qpEq_iff hden.2.2.2.1 hden_nxt.2.2.1).mp hcw
            have hcwp_rat : seg.wp1.toRat = nxt.wp0.toRat := (qpEq_iff hden.2.2.2.2.2.1 hden_nxt.2.2.2.2.1).mp hcwp
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · simp only [List.map_cons, checkChain, Bool.and_eq_true, beq_iff_eq]
              exact ⟨⟨⟨hcs_rat, hcw_rat⟩, hcwp_rat⟩, hchain_rest⟩
            · intro s' hm
              rcases List.mem_cons.mp hm with rfl | hm'
              · exact ⟨hds, hw1_eq, hwp1_eq, hwp0_le, hwp1_le, hw1_nn, hw0_le1, k, hs0_k,
                       fun hs0 hs1 hJ0 hJlo hJhi => hsup he0Lo he1Hi hs0 hs1 hJ0 hJlo hJhi⟩
              · exact hall_rest s' hm'
            · rcases hlast_rest with ⟨last, hgl, h1, h2, h3, h4⟩
              exact ⟨last, by simpa [List.getLast?] using hgl, h1, h2, h3, h4⟩
            · cases hm_rest with
              | inl hm =>
                simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
                cases hm with
                | inl hmIn => exact Or.inl hmIn
                | inr hcur =>
                  rcases hcur with ⟨hk_eq, hle⟩
                  refine Or.inr ⟨seg, List.mem_cons_self, ?_, (qpLe_iff hden.2.2.1 huM).mp hle⟩
                  change seg.toSpline.s0 = -42 / 100; rw [hs0_k, hk_eq]; grind
              | inr hm =>
                rcases hm with ⟨s', hmem', hs0', hw0'⟩
                exact Or.inr ⟨s', List.mem_cons_of_mem seg hmem', hs0', hw0'⟩
            · cases hz_rest with
              | inl hz =>
                simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hz
                cases hz with
                | inl hzIn => exact Or.inl hzIn
                | inr hcur =>
                  rcases hcur with ⟨hk_eq, hle⟩
                  refine Or.inr ⟨seg, List.mem_cons_self, ?_, (qpLe_iff hden.2.2.1 huZ).mp hle⟩
                  change seg.toSpline.s0 = 0; rw [hs0_k, hk_eq]; grind
              | inr hz =>
                rcases hz with ⟨s', hmem', hs0', hw0'⟩
                exact Or.inr ⟨s', List.mem_cons_of_mem seg hmem', hs0', hw0'⟩
          · simp [hstep] at hok

/-- **Main Bridge Theorem (`checkFullRawCert` → Exact `Rat` PDE Supersolution & Global Bounds)**:
    If the pure-integer kernel verifier `checkFullRawCert wCells r0sq segs uMouth uS0 = true`,
    and `E : Int → Rat` is ANY function satisfying `Exp50Spec E` (enclosing `exp(k/50)` at each
    step by `e50_step_enclosure`), then the exact `SplineCert` lifted from `segs` satisfies:
    1. Exact domain geometry `R0sq = 500 * wCells^2 / 286^2`;
    2. Left join (`s0 = -7/2`, `W = 1`, `W' < 0`) and right tail (`0 < W_M < 3/10`, `W' = 0`, `f(W_M) < 0`);
    3. Global monotonicity: `∀ sa ≤ sb, cert.evalSpline sb ≤ cert.evalSpline sa`;
    4. Global mouth & neck upper bounds:
       `∀ s ≥ -42/100, cert.evalSpline s ≤ uMouth.toRat` and
       `∀ s ≥ 0, cert.evalSpline s ≤ uS0.toRat`;
    5. Pointwise PDE supersolution on EVERY segment `sp ∈ cert.segs` for every `s ∈ [sp.s0, sp.s1]`
       and every Jacobian `J ≥ 0` enclosed by `C^2(E k - 1) ≤ J ≤ C^2(E (k+1) + 1)`. -/
theorem checkFullRawCert_sound {wCells : Nat} {r0sq uMouth uS0 : QPair} {segs : List RawSeg}
    (huM : 0 < uMouth.2) (huZ : 0 < uS0.2)
    (hok : checkFullRawCert wCells r0sq segs uMouth uS0 = true)
    {E : Int → Rat} (hE : Exp50Spec E) :
    let cert : SplineCert := ⟨wCells, r0sq.toRat, segs.map RawSeg.toSpline⟩
    cert.R0sq = (500 * ((wCells * wCells : Nat) : Rat)) / (286 * 286 : Rat) ∧
    (∃ first last,
      cert.segs.head? = some first ∧
      cert.segs.getLast? = some last ∧
      first.s0 = -7 / 2 ∧ first.w0 = 1 ∧ first.wp0 < 0 ∧
      (0 : Rat) < last.w1 ∧ last.w1 < 3 / 10 ∧ last.wp1 = 0 ∧
      nagumoF last.w1 < 0) ∧
    (∀ {sa sb : Rat}, sa ≤ sb → cert.evalSpline sb ≤ cert.evalSpline sa) ∧
    (∀ {s : Rat}, (-42 / 100 : Rat) ≤ s → cert.evalSpline s ≤ uMouth.toRat) ∧
    (∀ {s : Rat}, (0 : Rat) ≤ s → cert.evalSpline s ≤ uS0.toRat) ∧
    (∀ sp ∈ cert.segs,
      ∃ k : Int,
        sp.s0 = (k : Rat) / 100 ∧
        sp.s0 < sp.s1 ∧
        ∀ {s J : Rat},
          sp.s0 ≤ s → s ≤ sp.s1 →
          (0 : Rat) ≤ J →
          ((0 : Rat) < sp.s0 → certC2Lo cert.R0sq * (E k - 1) ≤ J) →
          (J ≤ certC2Hi cert.R0sq * (E (k + 1) + 1)) →
          (0 : Rat) ≤ sp.eval s ∧ sp.eval s ≤ 1 ∧ sp.c + J * nagumoF (sp.eval s) < 0) := by
  unfold checkFullRawCert at hok
  cases segs with
  | nil => simp at hok
  | cons first rest =>
    dsimp only at hok
    by_cases hpre : ((r0sq.2 != 0 && qpEq r0sq (500 * (wCells * wCells : Int), 286 * 286)) &&
        (qpEq first.s0 (-7, 2) && qpEq first.w0 (1, 1) && decide (first.wp0.1 < 0))) = true
    · simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hpre
      rcases hpre with ⟨⟨hr0ne, hr0eq⟩, ⟨⟨hfs0, hfw0⟩, hfwp0⟩⟩
      have hr0_pos : 0 < r0sq.2 := Nat.pos_of_ne_zero hr0ne
      have hr0_rat : r0sq.toRat = (500 * ((wCells * wCells : Nat) : Rat)) / (286 * 286 : Rat) := by
        have h := (qpEq_iff hr0_pos (by omega)).mp hr0eq
        rw [h]; unfold QPair.toRat
        have h1 : ((500 * (wCells * wCells : Int) : Int) : Rat) = 500 * ((wCells * wCells : Nat) : Rat) := by
          have := intCast_natCast_rat wCells; grind
        have h2 : ((286 * 286 : Nat) : Rat) = (286 * 286 : Rat) := by grind
        rw [h1, h2]
      have hr0_nn : 0 ≤ r0sq.1 := by
        unfold qpEq at hr0eq
        simp only [beq_iff_eq] at hr0eq
        have hmul : 0 ≤ 500 * ((wCells : Int) * (wCells : Int)) * (r0sq.2 : Int) := by
          have hw2 : 0 ≤ (wCells : Int) * (wCells : Int) := by
            have : (0 : Int) ≤ (wCells : Int) := Int.natCast_nonneg wCells
            exact Int.mul_nonneg this this
          have hd : (0 : Int) ≤ (r0sq.2 : Int) := Int.natCast_nonneg r0sq.2
          have := Int.mul_nonneg (by omega : (0 : Int) ≤ 500) hw2
          exact Int.mul_nonneg this hd
        have : 0 ≤ r0sq.1 * ((286 * 286 : Nat) : Int) := by omega
        omega
      have hgrid := expGridList_encloses hE
      have hloop := checkSegsLoop_sound hr0_pos hr0_nn huM huZ
        (first :: rest) (-350) expGridList false false (List.cons_ne_nil first rest) hgrid hok
      have hden_first := checkSegsLoop_head_pos_denoms hok
      clear hok hgrid
      rcases hloop with ⟨hchain, hall, ⟨last, hgl, hlw1_pos, hlw1_lt3, hlwp1_0, hftail⟩, hmOut, hzOut⟩
      have hfs0_rat : first.s0.toRat = -7 / 2 := by
        have := (qpEq_iff hden_first.1 (by omega)).mp hfs0
        have hm7 : QPair.toRat (-7, 2) = -7 / 2 := by unfold QPair.toRat; grind
        grind
      have hfw0_rat : first.w0.toRat = 1 := by
        have := (qpEq_iff hden_first.2.2.1 (by omega)).mp hfw0
        have ho : QPair.toRat (1, 1) = 1 := by unfold QPair.toRat; grind
        grind
      have hfwp0_rat : first.wp0.toRat < 0 := by
        have h : qpLt first.wp0 (0, 1) = true := by unfold qpLt; simp only [decide_eq_true_eq]; omega
        have := (qpLt_iff hden_first.2.2.2.2.1 (by omega)).mp h
        have hz : QPair.toRat (0, 1) = 0 := by unfold QPair.toRat; grind
        grind
      let cert : SplineCert := ⟨wCells, r0sq.toRat, (first :: rest).map RawSeg.toSpline⟩
      have hgl_map : cert.segs.getLast? = some last.toSpline := by
        change ((first :: rest).map RawSeg.toSpline).getLast? = some last.toSpline
        rw [List.getLast?_map, hgl]; rfl
      have hall_sp : ∀ sp ∈ cert.segs,
          sp.s0 < sp.s1 ∧
          sp.w1 = sp.w0 + sp.wp0 * (sp.s1 - sp.s0) + sp.c * ((sp.s1 - sp.s0) * (sp.s1 - sp.s0)) / 2 ∧
          sp.wp1 = sp.wp0 + sp.c * (sp.s1 - sp.s0) ∧
          sp.wp0 ≤ 0 ∧ sp.wp1 ≤ 0 := by
        intro sp hmem
        rcases List.mem_map.mp hmem with ⟨seg, hseg, rfl⟩
        rcases hall seg hseg with ⟨h1, h2, h3, h4, h5, _⟩
        exact ⟨h1, h2, h3, h4, h5⟩
      have hanti : ∀ {sa sb : Rat}, sa ≤ sb → cert.evalSpline sb ≤ cert.evalSpline sa := by
        intro sa sb hsab
        unfold SplineCert.evalSpline
        simp only [hgl_map]
        change (if sb ≤ first.s0.toRat then 1 else evalSegments cert.segs last.w1.toRat sb) ≤
               (if sa ≤ first.s0.toRat then 1 else evalSegments cert.segs last.w1.toRat sa)
        have htail_eq : (match cert.segs.getLast? with | some l => l.w1 = last.w1.toRat | none => True) := by
          rw [hgl_map]; rfl
        by_cases hsb : sb ≤ first.s0.toRat
        · have hsa : sa ≤ first.s0.toRat := by grind
          simp only [hsa, hsb, ↓reduceIte]; grind
        · by_cases hsa : sa ≤ first.s0.toRat
          · simp only [hsa, hsb, ↓reduceIte]
            have hle := evalSegments_antitone_aux cert.segs last.w1.toRat hchain hall_sp htail_eq
              (sa := first.s0.toRat) (sb := sb) Rat.le_refl (by grind)
            have hhead_eval : evalSegments cert.segs last.w1.toRat first.s0.toRat = 1 := by
              have h1 := evalSegments_at_knot cert.segs last.w1.toRat hchain
                (fun sp hm => ⟨(hall_sp sp hm).1, (hall_sp sp hm).2.1⟩) first.toSpline List.mem_cons_self
              simpa [RawSeg.toSpline, hfw0_rat] using h1
            grind
          · simp only [hsa, hsb, ↓reduceIte]
            have hsa_ge : first.s0.toRat ≤ sa := by grind
            exact evalSegments_antitone_aux cert.segs last.w1.toRat hchain hall_sp htail_eq
              hsa_ge hsab
      have heval_knot : ∀ seg ∈ first :: rest,
          (-7 / 2 : Rat) < seg.s0.toRat → cert.evalSpline seg.s0.toRat = seg.w0.toRat := by
        intro seg hmem hgt
        unfold SplineCert.evalSpline
        simp only [hgl_map]
        change (if seg.s0.toRat ≤ first.s0.toRat then 1 else evalSegments cert.segs last.w1.toRat seg.s0.toRat) =
               seg.w0.toRat
        have hnotle : ¬(seg.s0.toRat ≤ first.s0.toRat) := by rw [hfs0_rat]; grind
        simp only [hnotle, ↓reduceIte]
        exact evalSegments_at_knot cert.segs last.w1.toRat hchain
          (fun sp hm => ⟨(hall_sp sp hm).1, (hall_sp sp hm).2.1⟩) seg.toSpline
          (List.mem_map_of_mem hmem)
      refine ⟨hr0_rat,
        ⟨first.toSpline, last.toSpline, rfl, hgl_map, hfs0_rat, hfw0_rat, hfwp0_rat,
         hlw1_pos, hlw1_lt3, hlwp1_0, hftail⟩,
        hanti, ?_, ?_, ?_⟩
      · intro s hs
        rcases hmOut with hfalse | ⟨seg, hmem, hs0_eq, hw0_le⟩
        · cases hfalse
        · have hev := heval_knot seg hmem (by rw [hs0_eq]; grind)
          have hle := hanti (sa := seg.s0.toRat) (sb := s) (by rw [hs0_eq]; exact hs)
          grind
      · intro s hs
        rcases hzOut with hfalse | ⟨seg, hmem, hs0_eq, hw0_le⟩
        · cases hfalse
        · have hev := heval_knot seg hmem (by rw [hs0_eq]; grind)
          have hle := hanti (sa := seg.s0.toRat) (sb := s) (by rw [hs0_eq]; exact hs)
          grind
      · intro sp hmem
        rcases List.mem_map.mp hmem with ⟨seg, hseg, rfl⟩
        rcases hall seg hseg with ⟨hds, _, _, _, _, _, _, ki, hki, hsup⟩
        exact ⟨ki, hki, hds, hsup⟩
    · simp [hpre] at hok

end M44ContinuumPinning
