/-
  GSTheoremLib/Core/QPair.lean — Pure-Integer Exact Rational Pair Arithmetic & `Rat` Bridge

  Provides `QPair := Int × Nat` (representing `n / d` for `d > 0`) designed for fast
  Lean 4 kernel `decide` reduction (avoiding `Nat.gcd` and `Rat.div` opacity), together
  with complete order- and arithmetic-preserving bridge lemmas into native `Rat`.

  Zero external dependencies (pure Lean 4.36.0 `Init`), zero `sorry`, zero `native_decide`.
-/

namespace GSTheoremLib.Core

/-- Unreduced exact rational pair `(num, den)` representing `num / den` for `den > 0`. -/
abbrev QPair := Int × Nat

/-- Lift a `QPair` into native Lean `Rat`. -/
def QPair.toRat (q : QPair) : Rat :=
  (q.1 : Rat) / (q.2 : Rat)

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

/-! ## Cast & Order Bridges (`Nat` / `Int` → `Rat`) -/

theorem natCast_pos_rat {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => grind
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hcast : ((m + 2 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by grind
      grind

theorem intCast_natCast_rat (n : Nat) : ((n : Int) : Rat) = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : (((k + 1 : Nat) : Int) : Rat) = ((k : Int) : Rat) + 1 := by grind
    have h2 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h1, h2, ih]

theorem intCast_ofNat_rat (n : Nat) : ((Int.ofNat n : Int) : Rat) = (n : Rat) := by
  change ((n : Int) : Rat) = (n : Rat)
  exact intCast_natCast_rat n

theorem intCast_negSucc_rat (n : Nat) : ((Int.negSucc n : Int) : Rat) = -((n + 1 : Nat) : Rat) := by
  have h1 : (Int.negSucc n : Int) = -((n + 1 : Nat) : Int) := by omega
  rw [h1]
  have h2 : ((-((n + 1 : Nat) : Int) : Int) : Rat) = -(((n + 1 : Nat) : Int) : Rat) := by grind
  rw [h2, intCast_natCast_rat]

theorem intCast_rat_eq_iff {a b : Int} : (a : Rat) = (b : Rat) ↔ a = b := by
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

theorem intCast_rat_le_iff {a b : Int} : (a : Rat) ≤ (b : Rat) ↔ a ≤ b := by
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

theorem intCast_rat_lt_iff {a b : Int} : (a : Rat) < (b : Rat) ↔ a < b := by
  constructor
  · intro h
    have hle : a ≤ b := intCast_rat_le_iff.mp (by grind)
    have hne : a ≠ b := fun heq => by rw [heq] at h; grind
    omega
  · intro h
    have hle : (a : Rat) ≤ (b : Rat) := intCast_rat_le_iff.mpr (by omega)
    have hne : (a : Rat) ≠ (b : Rat) := fun heq => by have := intCast_rat_eq_iff.mp heq; omega
    grind

/-! ## `QPair` Operations Bridge to `Rat` -/

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
      have hne : (1 / ((a.2 : Rat) * (b.2 : Rat))) ≠ 0 := fun hz => by
        have hmul := congrArg (fun x => ((a.2 : Rat) * (b.2 : Rat)) * x) hz
        have hne' : (a.2 : Rat) * (b.2 : Rat) ≠ 0 := by grind
        grind
      grind
  constructor
  · intro h
    have hm := Rat.mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ 1 / ((a.2 : Rat) * (b.2 : Rat)))
    have ha0 : (a.2 : Rat) ≠ 0 := by grind
    have hb0 : (b.2 : Rat) ≠ 0 := by grind
    grind
  · intro h
    have hm := Rat.mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ (a.2 : Rat) * (b.2 : Rat))
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

end GSTheoremLib.Core
