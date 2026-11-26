/-
  Lean 4 Formalization of the Confirmed Theorem (M-23):
    "Exact-Rational (`Rat`) Monotonicity, All-Time Supersolution Comparison Principle,
     Nonzero Sensing Leak Margin, Fine-Grid (`h/2`) 5pt/9pt Instantiations,
     and Coupled Stencil Inheritance (`P2(u,v) + 9pt(a)`)"
  Source verdict:
    coordination/confirm/2026-11-22_m23_h2_rational_supersolution/VERDICT.md
    coordination/confirm/2026-11-22_m23_h2_rational_supersolution/CLAIM.md
  Revision (2026-11-24):
    Addresses all items from `sandbox/2026-11-24_agent3_lean_assumption_audit/REVIEW.md`:
    - Upgraded from fixed-denominator `Int` trajectories to genuine arbitrary-denominator
      exact rational (`Rat`) explicit Euler trajectories `a : Nat → ι → Rat`.
    - Removed the fixed-denominator divisibility assumption and scaling comment.
    - Explicitly instantiated `mkM23H2_5pt` and `mkM23H2_9pt` with exact M-23 `h/2`
      parameters (`h = 1/286, dt = 1/16, D_a = 1/100000, λ = 1/200, θ = 3/10, β = 1/50`).
    - Zero external dependencies (pure Lean 4.36.0 core `Init`, zero `sorry`).
-/

namespace M23Supersolution

/-! ## Part 1: Exact `Rat` Algebraic Lower Bound on the Bistable Nagumo Reaction -/

/-- Exact bistable Nagumo reaction function `f(x) = (1/200) * x * (1 - x) * (x - 3/10)`. -/
def nagumo (x : Rat) : Rat :=
  (1 / 200 : Rat) * x * (1 - x) * (x - 3 / 10)

theorem nagumo_zero : nagumo 0 = 0 := by unfold nagumo; grind

theorem nagumo_one : nagumo 1 = 0 := by unfold nagumo; grind

/-- Exact algebraic sum-of-nonnegatives identity on `Rat`:
    `nagumo b - nagumo a + (7/2000) * (b - a) = (b - a) * (1/2000) * P(a, b)`,
    where `P(a, b)` is manifestly a sum of nonnegative products on `[0, 1]^2`. -/
private theorem nagumo_diff_identity (a b : Rat) :
    nagumo b - nagumo a + (7 / 2000 : Rat) * (b - a) =
    (b - a) * ((1 / 2000 : Rat) *
      (10 * (1 - a) * a + 10 * (1 - b) * b +
       5 * (1 - a) * b + 5 * (1 - b) * a +
       2 * ((1 - a) + (1 - b)))) := by
  unfold nagumo
  grind

/-- Core Exact Rational Lemma:
    For all `a b : Rat` with `0 ≤ a ≤ b ≤ 1`,
      `-(7 / 2000) * (b - a) ≤ nagumo b - nagumo a`. -/
theorem nagumo_diff_lower_bound {a b : Rat}
    (ha0 : (0 : Rat) ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    -(7 / 2000 : Rat) * (b - a) ≤ nagumo b - nagumo a := by
  have ha1 : a ≤ 1 := by grind
  have hb0 : (0 : Rat) ≤ b := by grind
  have hba : (0 : Rat) ≤ b - a := by grind
  have h1a : (0 : Rat) ≤ 1 - a := by grind
  have h1b : (0 : Rat) ≤ 1 - b := by grind
  have t1 : (0 : Rat) ≤ 10 * (1 - a) * a :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) h1a) ha0
  have t2 : (0 : Rat) ≤ 10 * (1 - b) * b :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) h1b) hb0
  have t3 : (0 : Rat) ≤ 5 * (1 - a) * b :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) h1a) hb0
  have t4 : (0 : Rat) ≤ 5 * (1 - b) * a :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) h1b) ha0
  have t5 : (0 : Rat) ≤ 2 * ((1 - a) + (1 - b)) := by grind
  have hpoly : (0 : Rat) ≤
      (1 / 2000 : Rat) *
      (10 * (1 - a) * a + 10 * (1 - b) * b +
       5 * (1 - a) * b + 5 * (1 - b) * a +
       2 * ((1 - a) + (1 - b))) :=
    Rat.mul_nonneg (by grind) (by grind)
  have hprod : (0 : Rat) ≤
      (b - a) * ((1 / 2000 : Rat) *
      (10 * (1 - a) * a + 10 * (1 - b) * b +
       5 * (1 - a) * b + 5 * (1 - b) * a +
       2 * ((1 - a) + (1 - b)))) :=
    Rat.mul_nonneg hba hpoly
  rw [← nagumo_diff_identity a b] at hprod
  grind


/-! ## Part 2: Exact Rational Explicit Euler System on an Arbitrary Mask -/

/-- Exact rational (`Rat`) explicit Euler auxiliary reaction-diffusion system on an
    arbitrary mask index type `ι` with non-negative neighbor weights `w_ij ≥ 0`,
    time step `dt > 0`, and non-negative saturated sensing upper bound `sMax i ≥ 0`.
    At every cell `i`, one exact Euler step under sensing profile `s : ι → Rat` is:
      `step s a i = a i + ∑_{(j, w) ∈ nbs i} w * (a j - a i)
                        + dt * nagumo (a i) + s i * (1 - a i)`.
    Note: here `w` already absorbs `dt * D_a / h^2 * stencil_weight` and `s i` already
    absorbs `dt * β * c_d(i) * S(i)`. No fixed denominator is assumed; denominators may
    grow freely at every iteration. -/
structure RatAuxSystem (ι : Type) where
  dt : Rat
  hdt_pos : (0 : Rat) < dt
  nbs : ι → List (ι × Rat)
  hnbs_nonneg : ∀ i e, e ∈ nbs i → (0 : Rat) ≤ e.2
  sMax : ι → Rat
  hsMax_nonneg : ∀ i, (0 : Rat) ≤ sMax i
  /-- Exact center-monotonicity condition at every cell `i`:
      `1 - ∑_{(j, w) ∈ nbs i} w - dt * (7/2000) - sMax i ≥ 0`. -/
  hcenter_nonneg : ∀ i,
    (0 : Rat) ≤ 1 - (nbs i).foldl (fun acc e => acc + e.2) 0 - dt * (7 / 2000 : Rat) - sMax i

def RatAuxSystem.weightSum {ι : Type} (S : RatAuxSystem ι) (i : ι) : Rat :=
  (S.nbs i).foldl (fun acc e => acc + e.2) 0

/-- Exact rational explicit Euler one-step map `T_s(a)(i)`. -/
def RatAuxSystem.step {ι : Type} (S : RatAuxSystem ι)
    (s a : ι → Rat) (i : ι) : Rat :=
  a i
  + (S.nbs i).foldl (fun acc e => acc + e.2 * (a e.1 - a i)) 0
  + S.dt * nagumo (a i)
  + s i * (1 - a i)

private theorem foldl_diff_split {ι : Type} (a : ι → Rat) (c : Rat) :
    ∀ (es : List (ι × Rat)) (acc1 acc2 : Rat),
      es.foldl (fun acc e => acc + e.2 * (a e.1 - c)) (acc1 - acc2 * c) =
      es.foldl (fun acc e => acc + e.2 * a e.1) acc1 -
      es.foldl (fun acc e => acc + e.2) acc2 * c
  | [], _, _ => rfl
  | (j, w) :: es, acc1, acc2 => by
    simp only [List.foldl]
    have hstep : acc1 - acc2 * c + w * (a j - c) = (acc1 + w * a j) - (acc2 + w) * c := by grind
    rw [hstep]
    exact foldl_diff_split a c es (acc1 + w * a j) (acc2 + w)

private theorem foldl_weighted_mono {ι : Type} {a b : ι → Rat}
    (hab : ∀ j, a j ≤ b j) :
    ∀ (es : List (ι × Rat)) (acc1 acc2 : Rat),
      (∀ e ∈ es, (0 : Rat) ≤ e.2) → acc1 ≤ acc2 →
      es.foldl (fun acc e => acc + e.2 * a e.1) acc1 ≤
      es.foldl (fun acc e => acc + e.2 * b e.1) acc2
  | [], _, _, _, hacc => hacc
  | (j, w) :: es, acc1, acc2, hw, hacc => by
    simp only [List.foldl]
    apply foldl_weighted_mono hab es
    · intro e he; exact hw e (List.mem_cons_of_mem _ he)
    · have hw0 : (0 : Rat) ≤ w := hw (j, w) List.mem_cons_self
      have hmul : w * a j ≤ w * b j := Rat.mul_le_mul_of_nonneg_left (hab j) hw0
      grind

private theorem foldl_diff_const {ι : Type} (c : Rat) :
    ∀ (es : List (ι × Rat)) (acc : Rat),
      es.foldl (fun acc e => acc + e.2 * (c - c)) acc = acc
  | [], _ => rfl
  | (_, w) :: es, acc => by
    change es.foldl (fun acc e => acc + e.2 * (c - c)) (acc + w * (c - c)) = acc
    have h0 : acc + w * (c - c) = acc := by grind
    rw [h0]
    exact foldl_diff_const c es acc

/-- Theorem 2.1 (Order Preservation / Monotonicity in State on `[0, 1]`):
    For any sensing profile `s ≤ sMax`, if `0 ≤ a ≤ b ≤ 1` pointwise, then
    `S.step s a i ≤ S.step s b i` at every cell `i`. -/
theorem RatAuxSystem.step_monotone {ι : Type} (S : RatAuxSystem ι)
    {s a b : ι → Rat}
    (hs : ∀ i, s i ≤ S.sMax i)
    (ha0 : ∀ i, (0 : Rat) ≤ a i) (hab : ∀ i, a i ≤ b i) (hb1 : ∀ i, b i ≤ 1) (i : ι) :
    S.step s a i ≤ S.step s b i := by
  unfold RatAuxSystem.step
  have hsplit_a := foldl_diff_split a (a i) (S.nbs i) 0 0
  have hsplit_b := foldl_diff_split b (b i) (S.nbs i) 0 0
  have h0a : (0 : Rat) - (0 : Rat) * a i = 0 := by grind
  have h0b : (0 : Rat) - (0 : Rat) * b i = 0 := by grind
  rw [h0a] at hsplit_a
  rw [h0b] at hsplit_b
  rw [hsplit_a, hsplit_b]
  have hnb :
      (S.nbs i).foldl (fun acc e => acc + e.2 * a e.1) 0 ≤
      (S.nbs i).foldl (fun acc e => acc + e.2 * b e.1) 0 :=
    foldl_weighted_mono hab (S.nbs i) 0 0 (S.hnbs_nonneg i) (by grind)
  have hnag : -(7 / 2000 : Rat) * (b i - a i) ≤ nagumo (b i) - nagumo (a i) :=
    nagumo_diff_lower_bound (ha0 i) (hab i) (hb1 i)
  have hdt_nonneg : (0 : Rat) ≤ S.dt := by have := S.hdt_pos; grind
  have hdtnag : S.dt * (-(7 / 2000 : Rat) * (b i - a i)) ≤ S.dt * (nagumo (b i) - nagumo (a i)) :=
    Rat.mul_le_mul_of_nonneg_left hnag hdt_nonneg
  have hcenter := S.hcenter_nonneg i
  have hsi := hs i
  have hba : (0 : Rat) ≤ b i - a i := by have := hab i; grind
  have hcs : (0 : Rat) ≤
      (1 - (S.nbs i).foldl (fun acc e => acc + e.2) 0 - S.dt * (7 / 2000 : Rat) - s i) * (b i - a i) :=
    Rat.mul_nonneg (by grind) hba
  grind

/-- Theorem 2.2 (Monotonicity in Non-Negative Saturated Sensing Source):
    For any `a i ≤ 1`, increasing `s₁ i ≤ s₂ i` can only increase `S.step`. -/
theorem RatAuxSystem.step_monotone_in_source {ι : Type} (S : RatAuxSystem ι)
    {s₁ s₂ a : ι → Rat} (hs : ∀ i, s₁ i ≤ s₂ i) (ha1 : ∀ i, a i ≤ 1) (i : ι) :
    S.step s₁ a i ≤ S.step s₂ a i := by
  unfold RatAuxSystem.step
  have h1a : (0 : Rat) ≤ 1 - a i := by have := ha1 i; grind
  have hmul : (1 - a i) * s₁ i ≤ (1 - a i) * s₂ i :=
    Rat.mul_le_mul_of_nonneg_left (hs i) h1a
  grind

/-- Theorem 2.3 (`[0, 1]` Box Invariance): `step s 0 ≥ 0` and `step s 1 = 1`. -/
theorem RatAuxSystem.step_at_zero_nonneg {ι : Type} (S : RatAuxSystem ι)
    {s : ι → Rat} (hs0 : ∀ i, (0 : Rat) ≤ s i) (i : ι) :
    (0 : Rat) ≤ S.step s (fun _ => 0) i := by
  unfold RatAuxSystem.step
  rw [foldl_diff_const 0, nagumo_zero]
  have := hs0 i
  grind

theorem RatAuxSystem.step_at_one {ι : Type} (S : RatAuxSystem ι)
    (s : ι → Rat) (i : ι) :
    S.step s (fun _ => 1) i = 1 := by
  unfold RatAuxSystem.step
  rw [foldl_diff_const 1, nagumo_one]
  grind


/-! ## Part 3: M-23 All-Time Exact `Rat` Supersolution Comparison Principle -/

/-- Exact rational discrete residual `R_i(aBar) = (step sCap aBar i - aBar i) / dt`,
    here written directly as the non-positive step increment `step sCap aBar i - aBar i ≤ 0`. -/
def RatAuxSystem.stepIncrement {ι : Type} (S : RatAuxSystem ι)
    (sCap aBar : ι → Rat) (i : ι) : Rat :=
  S.step sCap aBar i - aBar i

/-- Main Confirmed Theorem (M-23 All-Time Exact `Rat` Comparison Principle):
    Valid for ANY exact rational explicit Euler trajectory `a : Nat → ι → Rat`
    (arbitrary denominator growth across arbitrarily many steps `n : Nat`), covering both
    the zero-source verdict and the nonzero leak-margin addendum (`0 ≤ s n i ≤ sCap i ≤ sMax i`). -/
theorem m23_all_time_supersolution_comparison {ι : Type} (S : RatAuxSystem ι)
    (drive : ι → Prop)
    (sCap aBar : ι → Rat)
    (hsCap_le : ∀ i, sCap i ≤ S.sMax i)
    (haBar_hi : ∀ i, aBar i ≤ 1)
    (haBar_drive : ∀ i, drive i → aBar i = 1)
    (haBar_res : ∀ i, ¬ drive i → S.stepIncrement sCap aBar i ≤ 0)
    (s : Nat → ι → Rat)
    (hs_nonneg : ∀ n i, (0 : Rat) ≤ s n i)
    (hs_le_cap : ∀ n i, s n i ≤ sCap i)
    (a : Nat → ι → Rat)
    (hinit_lo : ∀ i, (0 : Rat) ≤ a 0 i)
    (hinit_hi : ∀ i, a 0 i ≤ aBar i)
    (hdrive_step : ∀ n i, drive i → (0 : Rat) ≤ a (n + 1) i ∧ a (n + 1) i ≤ 1)
    (hnondrive_step : ∀ n i, ¬ drive i → a (n + 1) i = S.step (s n) (a n) i) :
    ∀ n i, (0 : Rat) ≤ a n i ∧ a n i ≤ aBar i := by
  intro n
  induction n with
  | zero =>
    intro i
    exact ⟨hinit_lo i, hinit_hi i⟩
  | succ n ih =>
    intro i
    have hlo_n : ∀ j, (0 : Rat) ≤ a n j := fun j => (ih j).1
    have hhi_n : ∀ j, a n j ≤ aBar j := fun j => (ih j).2
    have h1_n : ∀ j, a n j ≤ 1 := fun j => by have := hhi_n j; have := haBar_hi j; grind
    by_cases hd : drive i
    · have ⟨h0, h1⟩ := hdrive_step n i hd
      rw [haBar_drive i hd]
      exact ⟨h0, h1⟩
    · rw [hnondrive_step n i hd]
      have hsn_le_max : ∀ j, s n j ≤ S.sMax j :=
        fun j => by have := hs_le_cap n j; have := hsCap_le j; grind
      have ha_lo : (0 : Rat) ≤ S.step (s n) (a n) i := by
        have h0 := S.step_at_zero_nonneg (hs_nonneg n) i
        have hm := S.step_monotone hsn_le_max (fun _ => by decide) hlo_n h1_n i
        grind
      have h1 : S.step (s n) (a n) i ≤ S.step sCap (a n) i :=
        S.step_monotone_in_source (hs_le_cap n) h1_n i
      have h2 : S.step sCap (a n) i ≤ S.step sCap aBar i :=
        S.step_monotone hsCap_le hlo_n hhi_n haBar_hi i
      have h3 : S.step sCap aBar i ≤ aBar i := by
        have hres := haBar_res i hd
        unfold RatAuxSystem.stepIncrement at hres
        grind
      exact ⟨ha_lo, by grind⟩

/-- Corollary 3.1 (M-23 All-Time Subthreshold Pinning `a^n < 3/5 = 0.60` on `E2`). -/
theorem m23_all_time_subthreshold_pinning {ι : Type} (S : RatAuxSystem ι)
    (drive emit : ι → Prop)
    (sCap aBar : ι → Rat)
    (hsCap_le : ∀ i, sCap i ≤ S.sMax i)
    (haBar_hi : ∀ i, aBar i ≤ 1)
    (haBar_drive : ∀ i, drive i → aBar i = 1)
    (haBar_res : ∀ i, ¬ drive i → S.stepIncrement sCap aBar i ≤ 0)
    (haBar_emit_lt : ∀ i, emit i → aBar i < 3 / 5)
    (s : Nat → ι → Rat)
    (hs_nonneg : ∀ n i, (0 : Rat) ≤ s n i)
    (hs_le_cap : ∀ n i, s n i ≤ sCap i)
    (a : Nat → ι → Rat)
    (hinit_lo : ∀ i, (0 : Rat) ≤ a 0 i)
    (hinit_hi : ∀ i, a 0 i ≤ aBar i)
    (hdrive_step : ∀ n i, drive i → (0 : Rat) ≤ a (n + 1) i ∧ a (n + 1) i ≤ 1)
    (hnondrive_step : ∀ n i, ¬ drive i → a (n + 1) i = S.step (s n) (a n) i) :
    ∀ n i, emit i → a n i < 3 / 5 := by
  intro n i hemit
  have hcomp := (m23_all_time_supersolution_comparison S drive sCap aBar
    hsCap_le haBar_hi haBar_drive haBar_res
    s hs_nonneg hs_le_cap a hinit_lo hinit_hi hdrive_step hnondrive_step n i).2
  have hlt := haBar_emit_lt i hemit
  grind


/-! ## Part 4: Concrete M-23 Fine-Grid (`h = 1/286, dt = 1/16`) `5pt` & `9pt` System Constructors -/

/-- Exact M-23 fine-grid parameters: `h = 1/286`, `D_a = 10^-5`, `μ = D_a/h^2 = 20449/25000`,
    `dt = 1/16`, `β = 1/50 = 0.02`, so `dt * μ = 20449 / 400000` and `dt * β = 1 / 800`. -/
def m23_dt : Rat := 1 / 16
def m23_mu : Rat := (286 * 286 : Rat) / 100000
def m23_beta : Rat := 1 / 50
def m23_leak_s : Rat := 9999 / 1000000000

theorem m23_h2_exact_center_slopes :
    (1 - 4 * (m23_dt * m23_mu) - m23_dt * (7 / 2000 : Rat)) = (636233 / 800000 : Rat) ∧
    (1 - (10 / 3 : Rat) * (m23_dt * m23_mu) - m23_dt * (7 / 2000 : Rat)) = (398099 / 480000 : Rat) ∧
    (636233 / 800000 : Rat) > (7952 / 10000 : Rat) ∧
    (398099 / 480000 : Rat) > (8293 / 10000 : Rat) ∧
    (636233 / 800000 : Rat) - m23_dt * m23_beta * 1 > 0 ∧
    (398099 / 480000 : Rat) - m23_dt * m23_beta * 1 > 0 ∧
    (636233 / 800000 : Rat) - m23_dt * m23_beta * m23_leak_s > 0 ∧
    (398099 / 480000 : Rat) - m23_dt * m23_beta * m23_leak_s > 0 := by
  unfold m23_dt m23_mu m23_beta m23_leak_s
  grind

/-- Concrete constructor for ANY M-23 `h/2` `5pt` zero-flux mask (where each cell has
    total neighbor weight `≤ 4 * dt * μ` and sensing bound `sMax i ≤ dt * β = 1/800`,
    covering both `s = 0`, the `VERDICT.md` addendum `s ≤ 9999/10^9`, and full sensing `s ≤ 1`). -/
def mkM23H2_5pt {ι : Type}
    (nbs : ι → List (ι × Rat))
    (hnbs_nonneg : ∀ i e, e ∈ nbs i → (0 : Rat) ≤ e.2)
    (hnbs_sum : ∀ i, (nbs i).foldl (fun acc e => acc + e.2) 0 ≤ 4 * (m23_dt * m23_mu))
    (sMax : ι → Rat)
    (hsMax_nonneg : ∀ i, (0 : Rat) ≤ sMax i)
    (hsMax_le : ∀ i, sMax i ≤ m23_dt * m23_beta) : RatAuxSystem ι where
  dt := m23_dt
  hdt_pos := by unfold m23_dt; grind
  nbs := nbs
  hnbs_nonneg := hnbs_nonneg
  sMax := sMax
  hsMax_nonneg := hsMax_nonneg
  hcenter_nonneg := by
    intro i
    have hw := hnbs_sum i
    have hs := hsMax_le i
    have hconst : (0 : Rat) ≤
        1 - 4 * (m23_dt * m23_mu) - m23_dt * (7 / 2000 : Rat) - m23_dt * m23_beta := by
      unfold m23_dt m23_mu m23_beta; grind
    grind

/-- Concrete constructor for ANY M-23 `h/2` `9pt` zero-flux mask (where each cell has
    total neighbor weight `≤ (10/3) * dt * μ` and sensing bound `sMax i ≤ dt * β = 1/800`). -/
def mkM23H2_9pt {ι : Type}
    (nbs : ι → List (ι × Rat))
    (hnbs_nonneg : ∀ i e, e ∈ nbs i → (0 : Rat) ≤ e.2)
    (hnbs_sum : ∀ i, (nbs i).foldl (fun acc e => acc + e.2) 0 ≤ (10 / 3 : Rat) * (m23_dt * m23_mu))
    (sMax : ι → Rat)
    (hsMax_nonneg : ∀ i, (0 : Rat) ≤ sMax i)
    (hsMax_le : ∀ i, sMax i ≤ m23_dt * m23_beta) : RatAuxSystem ι where
  dt := m23_dt
  hdt_pos := by unfold m23_dt; grind
  nbs := nbs
  hnbs_nonneg := hnbs_nonneg
  sMax := sMax
  hsMax_nonneg := hsMax_nonneg
  hcenter_nonneg := by
    intro i
    have hw := hnbs_sum i
    have hs := hsMax_le i
    have hconst : (0 : Rat) ≤
        1 - (10 / 3 : Rat) * (m23_dt * m23_mu) - m23_dt * (7 / 2000 : Rat) - m23_dt * m23_beta := by
      unfold m23_dt m23_mu m23_beta; grind
    grind


/-! ## Part 5: Conditional Coupled Stencil Inheritance (`P2(u,v) + 9pt(a)`) -/

/-- Conditional inheritance theorem (`CLAIM.md` Proposition 2):
    For any external state trajectory `uvTraj : Nat → State` (e.g. Gray–Scott `(u, v)` under
    `5pt`, `9pt`, or `P2`), **provided** its saturated sensing entering the monotone `Rat`
    auxiliary map satisfies `0 ≤ sense (uvTraj n) i ≤ sCap i ≤ sMax i` at every step `n`,
    the exact same all-time subthreshold pinning bound `a n i < 3/5` holds.
    (Note: this theorem does not prove that a specific GS/P2 trajectory satisfies `hsense_le_cap`.) -/
theorem m23_coupled_stencil_inheritance {ι State : Type} (S : RatAuxSystem ι)
    (drive emit : ι → Prop)
    (sCap aBar : ι → Rat)
    (hsCap_le : ∀ i, sCap i ≤ S.sMax i)
    (haBar_hi : ∀ i, aBar i ≤ 1)
    (haBar_drive : ∀ i, drive i → aBar i = 1)
    (haBar_res : ∀ i, ¬ drive i → S.stepIncrement sCap aBar i ≤ 0)
    (haBar_emit_lt : ∀ i, emit i → aBar i < 3 / 5)
    (uvTraj : Nat → State)
    (sense : State → ι → Rat)
    (hsense_nonneg : ∀ n i, (0 : Rat) ≤ sense (uvTraj n) i)
    (hsense_le_cap : ∀ n i, sense (uvTraj n) i ≤ sCap i)
    (a : Nat → ι → Rat)
    (hinit_lo : ∀ i, (0 : Rat) ≤ a 0 i)
    (hinit_hi : ∀ i, a 0 i ≤ aBar i)
    (hdrive_step : ∀ n i, drive i → (0 : Rat) ≤ a (n + 1) i ∧ a (n + 1) i ≤ 1)
    (hnondrive_step : ∀ n i, ¬ drive i → a (n + 1) i = S.step (sense (uvTraj n)) (a n) i) :
    ∀ n i, emit i → a n i < 3 / 5 :=
  m23_all_time_subthreshold_pinning S drive emit sCap aBar
    hsCap_le haBar_hi haBar_drive haBar_res haBar_emit_lt
    (fun n => sense (uvTraj n)) hsense_nonneg hsense_le_cap
    a hinit_lo hinit_hi hdrive_step hnondrive_step

end M23Supersolution
