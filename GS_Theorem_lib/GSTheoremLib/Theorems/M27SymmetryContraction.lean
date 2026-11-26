/-
  GSTheoremLib/Theorems/M27SymmetryContraction.lean — Formalization of M-27 / M-15:
    "Nonlinear Lateral-Symmetry Contraction Theorem & Critical Symmetrizing Width
     for 2D Bistable Nagumo Channels (Continuum Constants + Discrete 5pt/9pt)"

  Source notes & verification script:
    sandbox/2026-11-23_agent3_m27_symmetry_contraction_theorem/NOTE.md
    sandbox/2026-11-23_agent3_m27_symmetry_contraction_theorem/verify_m27_contraction.py

  Reuses `GSTheoremLib.Core.{QPair, Nagumo, Enclosure}`.
  Zero Mathlib, zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import GSTheoremLib.Core.QPair
import GSTheoremLib.Core.Nagumo
import GSTheoremLib.Core.Enclosure

namespace M27SymmetryContraction

open GSTheoremLib.Core

/-! ## Part 1: Exact Global Slope & Symmetric Secant Bounds (Lemma 1 of M-27) -/

/-- Exact global upper slope constant `f'_max = 79 / 60000` for `nagumoScaled`. -/
def fPrimeMax : Rat := 79 / 60000

/-- Exact global lower slope constant `f'_min = -7 / 2000` for `nagumoScaled`. -/
def fPrimeMin : Rat := -(7 / 2000)

/-- Exact project diffusion coefficient `D_a = 1 / 100000`. -/
def diffDa : Rat := 1 / 100000

/-- Exact one-sided upper Lipschitz bound for `nagumoScaled` on all of `Rat`:
    reuses `GSTheoremLib.Core.nagumoUnit_one_sided_lipschitz` (`K = 79 / 300`). -/
theorem nagumoScaled_one_sided_upper {a b : Rat} (hab : b ≤ a) :
    nagumoScaled a - nagumoScaled b ≤ fPrimeMax * (a - b) := by
  rw [nagumoScaled_eq_unit a, nagumoScaled_eq_unit b]
  have h := nagumoUnit_one_sided_lipschitz hab
  unfold fPrimeMax
  grind

/-- Exact one-sided lower Lipschitz bound for `nagumoScaled` on `[0, 1]`:
    for `0 ≤ b ≤ a ≤ 1`, `-(7 / 2000) * (a - b) ≤ nagumoScaled a - nagumoScaled b`. -/
theorem nagumoScaled_one_sided_lower {a b : Rat}
    (hb0 : (0 : Rat) ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    fPrimeMin * (a - b) ≤ nagumoScaled a - nagumoScaled b := by
  rw [nagumoScaled_eq_unit a, nagumoScaled_eq_unit b]
  unfold nagumoUnit M44ContinuumPinning.nagumoF fPrimeMin
  let u : Rat := 1 - a
  let v : Rat := 1 - b
  have hu0 : (0 : Rat) ≤ u := by grind
  have hv0 : (0 : Rat) ≤ v := by grind
  have hu1 : u ≤ 1 := by grind
  have hv1 : v ≤ 1 := by grind
  have hterm1 : (0 : Rat) ≤ u * ((17 / 10 : Rat) - u - v / 2) :=
    Rat.mul_nonneg hu0 (by grind)
  have hterm2 : (0 : Rat) ≤ v * ((17 / 10 : Rat) - v - u / 2) :=
    Rat.mul_nonneg hv0 (by grind)
  have hquad : (0 : Rat) ≤ (1 / 200 : Rat) * (u * ((17 / 10 : Rat) - u - v / 2) +
      v * ((17 / 10 : Rat) - v - u / 2)) := by grind
  have hprod := Rat.mul_nonneg hquad (by grind : (0 : Rat) ≤ a - b)
  have hid : (1 / 200 : Rat) * (a * (1 - a) * (a - 3 / 10)) -
      (1 / 200 : Rat) * (b * (1 - b) * (b - 3 / 10)) - (-(7 / 2000 : Rat)) * (a - b) =
      (1 / 200 : Rat) * (u * ((17 / 10 : Rat) - u - v / 2) +
        v * ((17 / 10 : Rat) - v - u / 2)) * (a - b) := by
    simp only [u, v]; grind
  grind

/-- Exact secant slope `q(a, b) = (g(a) - g(b)) / (a - b)` for `a ≠ b`. -/
def secantSlope (a b : Rat) : Rat :=
  if a = b then fPrimeMax else (nagumoScaled a - nagumoScaled b) / (a - b)

/-- Symmetry (evenness under `x ↦ -x` swap): `secantSlope a b = secantSlope b a`. -/
theorem secantSlope_symm (a b : Rat) : secantSlope a b = secantSlope b a := by
  unfold secantSlope
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := fun heq => h heq.symm
    simp only [h, h', ↓reduceIte]
    have hne : a - b ≠ 0 := by grind
    have hne' : b - a ≠ 0 := by grind
    grind

/-- Exact secant identity: `nagumoScaled a - nagumoScaled b = secantSlope a b * (a - b)`. -/
private theorem rat_one_div_pos {x : Rat} (hx : (0 : Rat) < x) : (0 : Rat) < 1 / x := by
  have hne : x ≠ 0 := by grind
  have hmul1 : x * (1 / x) = 1 := by grind
  cases @Rat.le_total (1 / x) 0 with
  | inl hle =>
    exfalso
    have hm := Rat.mul_le_mul_of_nonneg_left hle (by grind : (0 : Rat) ≤ x)
    rw [hmul1] at hm; grind
  | inr hge =>
    have hinv_ne : (1 / x) ≠ 0 := fun hz => by rw [hz] at hmul1; grind
    grind

theorem secantSlope_mul (a b : Rat) :
    nagumoScaled a - nagumoScaled b = secantSlope a b * (a - b) := by
  unfold secantSlope
  by_cases h : a = b
  · subst h; grind
  · simp only [h, ↓reduceIte]
    have hne : a - b ≠ 0 := by grind
    grind

/-- Lemma 1 (Global Secant Slope Enclosure on `[0, 1]`):
    For ALL `a, b ∈ [0, 1]`, `fPrimeMin ≤ secantSlope a b ≤ fPrimeMax`. -/
theorem secantSlope_bounds {a b : Rat}
    (ha0 : (0 : Rat) ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Rat) ≤ b) (hb1 : b ≤ 1) :
    fPrimeMin ≤ secantSlope a b ∧ secantSlope a b ≤ fPrimeMax := by
  unfold secantSlope
  by_cases h : a = b
  · simp only [h, ↓reduceIte]
    unfold fPrimeMin fPrimeMax; grind
  · simp only [h, ↓reduceIte]
    cases @Rat.le_total b a with
    | inl hba =>
      have hpos : (0 : Rat) < a - b := by grind
      have hlo := nagumoScaled_one_sided_lower hb0 hba ha1
      have hhi := nagumoScaled_one_sided_upper hba
      have hinv : (0 : Rat) ≤ 1 / (a - b) := by have := rat_one_div_pos hpos; grind
      have h1 := Rat.mul_le_mul_of_nonneg_right hlo hinv
      have h2 := Rat.mul_le_mul_of_nonneg_right hhi hinv
      have hne : a - b ≠ 0 := by grind
      grind
    | inr hab =>
      have hpos : (0 : Rat) < b - a := by grind
      have hlo := nagumoScaled_one_sided_lower ha0 hab hb1
      have hhi := nagumoScaled_one_sided_upper hab
      have hinv : (0 : Rat) ≤ 1 / (b - a) := by have := rat_one_div_pos hpos; grind
      have h1 := Rat.mul_le_mul_of_nonneg_right hlo hinv
      have h2 := Rat.mul_le_mul_of_nonneg_right hhi hinv
      have hne : b - a ≠ 0 := by grind
      have hne' : a - b ≠ 0 := by grind
      grind


/-! ## Part 2: Exact Critical Symmetrizing Width `W_sym = π √(3 / 395)` (Theorem 1 Constants) -/

/-- Verified rational lower/upper bounds on `π` (`M44ContinuumPinning.pi_machin_enclosure`). -/
def piLoRat : Rat := 314159265 / 100000000
def piHiRat : Rat := 314159266 / 100000000

/-- Exact ratio `D_a / f'_max = 3 / 395`. -/
theorem diffDa_div_fPrimeMax : diffDa / fPrimeMax = (3 / 395 : Rat) := by
  unfold diffDa fPrimeMax; grind

/-- Exact physical critical width enclosure:
    `0.27378645 < W_sym = π √(3/395) < 0.27378646`. -/
theorem m27_critical_width_phys_enclosure :
    ((27378645 / 100000000 : Rat) * (27378645 / 100000000 : Rat) <
      piLoRat * piLoRat * (3 / 395 : Rat)) ∧
    (piHiRat * piHiRat * (3 / 395 : Rat) <
      (27378646 / 100000000 : Rat) * (27378646 / 100000000 : Rat)) := by
  unfold piLoRat piHiRat; grind

/-- Exact baseline-grid (`h_0 = 1/143`) critical width enclosure in cells:
    `39.151462 < W_sym / h_0 < 39.151463`. -/
theorem m27_critical_width_cells_enclosure :
    ((39151462 / 1000000 : Rat) * (39151462 / 1000000 : Rat) <
      (143 * piLoRat) * (143 * piLoRat) * (3 / 395 : Rat)) ∧
    ((143 * piHiRat) * (143 * piHiRat) * (3 / 395 : Rat) <
      (39151463 / 1000000 : Rat) * (39151463 / 1000000 : Rat)) := by
  unfold piLoRat piHiRat; grind

/-- Continuum net damping rate `γ_lo(w) = D_a (π_lo / (w/143))^2 - f'_max` is strictly positive
    for every integer width `1 ≤ w ≤ 39`. -/
theorem m27_continuum_gamma_pos_le39 {w : Nat} (hw1 : 1 ≤ w) (hw39 : w ≤ 39) :
    (0 : Rat) < diffDa * ((piLoRat / ((w : Rat) / 143)) * (piLoRat / ((w : Rat) / 143))) - fPrimeMax := by
  have hw_pos : (0 : Rat) < (w : Rat) := natCast_pos_rat (by omega)
  have hw_le : (w : Rat) ≤ 39 := by
    have h : (w : Int) ≤ 39 := by omega
    have h' := intCast_rat_le_iff.mpr h
    rw [intCast_natCast_rat] at h'
    exact h'
  have hsq : (w : Rat) * (w : Rat) ≤ 39 * 39 := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hw_le (by grind : (0 : Rat) ≤ (w : Rat))
    have h2 := Rat.mul_le_mul_of_nonneg_right hw_le (by grind : (0 : Rat) ≤ (39 : Rat))
    grind
  have h39 : (39 * 39 : Rat) * fPrimeMax < diffDa * (143 * piLoRat) * (143 * piLoRat) := by
    unfold diffDa fPrimeMax piLoRat; grind
  have hnum : (w : Rat) * (w : Rat) * fPrimeMax < diffDa * (143 * piLoRat) * (143 * piLoRat) := by
    have hfm : (0 : Rat) ≤ fPrimeMax := by unfold fPrimeMax; grind
    have hm := Rat.mul_le_mul_of_nonneg_right hsq hfm
    grind
  have hw2_pos : (0 : Rat) < (w : Rat) * (w : Rat) := Rat.mul_pos hw_pos hw_pos
  have hinv_pos : (0 : Rat) < 1 / ((w : Rat) * (w : Rat)) := rat_one_div_pos hw2_pos
  have hmul := Rat.mul_pos (by grind : (0 : Rat) < diffDa * (143 * piLoRat) * (143 * piLoRat) -
      (w : Rat) * (w : Rat) * fPrimeMax) hinv_pos
  have hw_ne : (w : Rat) ≠ 0 := by grind
  have hre : (diffDa * (143 * piLoRat) * (143 * piLoRat) - (w : Rat) * (w : Rat) * fPrimeMax) *
      (1 / ((w : Rat) * (w : Rat))) =
      diffDa * ((piLoRat / ((w : Rat) / 143)) * (piLoRat / ((w : Rat) / 143))) - fPrimeMax := by
    grind
  rw [← hre]; exact hmul

/-- At `w = 40 > W_sym`, the continuum damping upper bound is strictly negative. -/
theorem m27_continuum_gamma_neg_40 :
    diffDa * ((piHiRat / ((40 : Rat) / 143)) * (piHiRat / ((40 : Rat) / 143))) - fPrimeMax < 0 := by
  unfold diffDa fPrimeMax piHiRat; grind


/-! ## Part 3: General All-Time Discrete Spatial Barrier Theorem (Theorem 2 of M-27) -/

/-- Exact rational power `r ^ n` by structural recursion. -/
def ratPow (r : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => r * ratPow r n

theorem ratPow_pos {r : Rat} (hr : (0 : Rat) < r) (n : Nat) : (0 : Rat) < ratPow r n := by
  induction n with
  | zero => simp [ratPow]; decide
  | succ k ih => exact Rat.mul_pos hr ih

theorem ratPow_add (r : Rat) (a b : Nat) :
    ratPow r (a + b) = ratPow r a * ratPow r b := by
  induction a with
  | zero => simp [ratPow]
  | succ k ih =>
    have : k + 1 + b = (k + b) + 1 := by omega
    rw [this, ratPow, ratPow, ih]; grind

/-- Exact finite-neck closed-Neumann spatial barrier profile:
    `B_j = H0 * (r^j + r^(2L - 1 - j)) / (1 + r^(2L - 1))`. -/
def neumannBarrier (H0 r : Rat) (L j : Nat) : Rat :=
  H0 * (ratPow r j + ratPow r (2 * L - 1 - j)) / (1 + ratPow r (2 * L - 1))

theorem neumannBarrier_nonneg {H0 r : Rat} (hH0 : (0 : Rat) ≤ H0) (hr : (0 : Rat) < r) (L j : Nat) :
    (0 : Rat) ≤ neumannBarrier H0 r L j := by
  unfold neumannBarrier
  have h1 := ratPow_pos hr j
  have h2 := ratPow_pos hr (2 * L - 1 - j)
  have h3 := ratPow_pos hr (2 * L - 1)
  have hnum : (0 : Rat) ≤ H0 * (ratPow r j + ratPow r (2 * L - 1 - j)) :=
    Rat.mul_nonneg hH0 (by grind)
  have hden : (0 : Rat) < 1 + ratPow r (2 * L - 1) := by grind
  have hinv : (0 : Rat) ≤ 1 / (1 + ratPow r (2 * L - 1)) := by
    cases @Rat.le_total (1 / (1 + ratPow r (2 * L - 1))) 0 with
    | inl hle =>
      exfalso
      have hm := Rat.mul_le_mul_of_nonneg_left hle (by grind : (0 : Rat) ≤ 1 + ratPow r (2 * L - 1))
      have hne : 1 + ratPow r (2 * L - 1) ≠ 0 := by grind
      grind
    | inr hge => exact hge
  have hm := Rat.mul_nonneg hnum hinv
  grind

/-- Exact entrance identity: at `j = 0`, `neumannBarrier H0 r L 0 = H0`. -/
theorem neumannBarrier_at_zero {H0 r : Rat} (hr : (0 : Rat) < r) (L : Nat) :
    neumannBarrier H0 r L 0 = H0 := by
  unfold neumannBarrier
  have h3 := ratPow_pos hr (2 * L - 1)
  have hne : 1 + ratPow r (2 * L - 1) ≠ 0 := by grind
  simp only [Nat.sub_zero, ratPow]
  grind

/-- Exact discrete Neumann reflection identity at the closed exit `j = L - 1`:
    the ghost row `j = L` has the exact same barrier value as `j = L - 1`. -/
theorem neumannBarrier_neumann_bc (H0 r : Rat) {L : Nat} (hL : 1 ≤ L) :
    neumannBarrier H0 r L L = neumannBarrier H0 r L (L - 1) := by
  unfold neumannBarrier
  have h1 : 2 * L - 1 - L = L - 1 := by omega
  have h2 : 2 * L - 1 - (L - 1) = L := by omega
  rw [h1, h2]; grind

/-- Exact 3-point algebraic eigenrelation for `neumannBarrier`:
    for every `1 ≤ j < L`, `B(j - 1) + B(j + 1) = (r + 1 / r) * B(j)`. -/
theorem neumannBarrier_neighbor_sum {H0 r : Rat} (hr : (0 : Rat) < r) {L j : Nat}
    (hj1 : 1 ≤ j) (hjL : j < L) :
    neumannBarrier H0 r L (j - 1) + neumannBarrier H0 r L (j + 1) =
      (r + 1 / r) * neumannBarrier H0 r L j := by
  unfold neumannBarrier
  have h3 := ratPow_pos hr (2 * L - 1)
  have hdne : 1 + ratPow r (2 * L - 1) ≠ 0 := by grind
  have hrne : r ≠ 0 := by grind
  have hp1 : ratPow r j = r * ratPow r (j - 1) := by
    cases hj : j with | zero => omega | succ m => simp [ratPow]
  have hp2 : ratPow r (j + 1) = r * ratPow r j := rfl
  have hp3 : ratPow r (2 * L - 1 - (j - 1)) = r * ratPow r (2 * L - 1 - j) := by
    have hk : 2 * L - 1 - (j - 1) = (2 * L - 1 - j) + 1 := by omega
    rw [hk]; rfl
  have hp4 : ratPow r (2 * L - 1 - j) = r * ratPow r (2 * L - 1 - (j + 1)) := by
    have hk : 2 * L - 1 - j = (2 * L - 1 - (j + 1)) + 1 := by omega
    rw [hk]; rfl
  rw [hp2, hp3, hp4, hp1]
  grind

/-- Exact one-step discrete supersolution invariance of `neumannBarrier` at every interior & exit row:
    if `mu_eff * (r + 1 / r - 2) ≤ gamma`, then the positive-coefficient row update maps `B` to `≤ B`. -/
theorem neumannBarrier_step_invariant {H0 r mu_eff dt gamma : Rat}
    (hH0 : (0 : Rat) ≤ H0) (hr : (0 : Rat) < r) (hdt : (0 : Rat) ≤ dt)
    (hbar : mu_eff * (r + 1 / r - 2) ≤ gamma)
    {L j : Nat} (hj1 : 1 ≤ j) (hjL : j < L) :
    let B := neumannBarrier H0 r L
    let rightB := if j + 1 < L then B (j + 1) else B (L - 1)
    (1 - 2 * mu_eff * dt - dt * gamma) * B j + mu_eff * dt * (B (j - 1) + rightB) ≤ B j := by
  intro B rightB
  have hright : rightB = B (j + 1) := by
    simp only [rightB]
    split
    · rfl
    · have hj_last : j = L - 1 := by omega
      have hjl : j + 1 = L := by omega
      rw [hjl]
      exact (neumannBarrier_neumann_bc H0 r (by omega)).symm
  rw [hright]
  have hsum : B (j - 1) + B (j + 1) = (r + 1 / r) * B j :=
    neumannBarrier_neighbor_sum hr hj1 hjL
  rw [hsum]
  have hBj : (0 : Rat) ≤ B j := neumannBarrier_nonneg hH0 hr L j
  have hdiff : mu_eff * (r + 1 / r - 2) - gamma ≤ 0 := by grind
  have hdt_neg : dt * (mu_eff * (r + 1 / r - 2) - gamma) ≤ 0 := by
    have h := Rat.mul_nonneg hdt (by grind : (0 : Rat) ≤ -(mu_eff * (r + 1 / r - 2) - gamma))
    grind
  have hprod : dt * (mu_eff * (r + 1 / r - 2) - gamma) * B j ≤ 0 := by
    have h := Rat.mul_nonneg (by grind : (0 : Rat) ≤ -(dt * (mu_eff * (r + 1 / r - 2) - gamma))) hBj
    grind
  grind

/-- **Main Theorem 2 (All-Time Discrete Nonlinear Spatial Symmetry Contraction)**:
    For ANY neck length `L ≥ 1`, positive-coefficient row update `(mu_eff, dt, gamma)` satisfying
    `0 ≤ 1 - 2 * mu_eff * dt - dt * gamma` and `mu_eff * (r + 1 / r - 2) ≤ gamma`, and ANY
    row-norm trajectory `H : Nat → Fin L → Rat` starting at `H 0 ≤ B` with arbitrary time-varying
    asymmetric entrance `H n 0 ≤ H0` and closed Neumann exit:
      `∀ n : Nat, ∀ j : Fin L, H n j ≤ neumannBarrier H0 r L j.1`. -/
theorem m27_discrete_all_time_spatial_contraction
    {L : Nat} (hL : 1 ≤ L)
    {H0 r mu_eff dt gamma : Rat}
    (hH0 : (0 : Rat) ≤ H0) (hr : (0 : Rat) < r)
    (hmu : (0 : Rat) ≤ mu_eff) (hdt : (0 : Rat) ≤ dt)
    (hdiag : (0 : Rat) ≤ 1 - 2 * mu_eff * dt - dt * gamma)
    (hbar : mu_eff * (r + 1 / r - 2) ≤ gamma)
    (H : Nat → Fin L → Rat)
    (hinit : ∀ j : Fin L, H 0 j ≤ neumannBarrier H0 r L j.1)
    (hentrance : ∀ n : Nat, H n ⟨0, by omega⟩ ≤ H0)
    (hstep : ∀ (n : Nat) (j : Fin L), 1 ≤ j.1 →
      let leftH := H n ⟨j.1 - 1, by omega⟩
      let rightH := if h : j.1 + 1 < L then H n ⟨j.1 + 1, h⟩ else H n ⟨L - 1, by omega⟩
      H (n + 1) j ≤ (1 - 2 * mu_eff * dt - dt * gamma) * H n j + mu_eff * dt * (leftH + rightH)) :
    ∀ (n : Nat) (j : Fin L), H n j ≤ neumannBarrier H0 r L j.1 := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
    intro j
    by_cases hj0 : j.1 = 0
    · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hj_eq, neumannBarrier_at_zero hr L]
      exact hentrance (k + 1)
    · have hj1 : 1 ≤ j.1 := by omega
      have hst := hstep k j hj1
      have hleft : H k ⟨j.1 - 1, by omega⟩ ≤ neumannBarrier H0 r L (j.1 - 1) := ih ⟨j.1 - 1, by omega⟩
      have hmid : H k j ≤ neumannBarrier H0 r L j.1 := ih j
      have hright : (if h : j.1 + 1 < L then H k ⟨j.1 + 1, h⟩ else H k ⟨L - 1, by omega⟩) ≤
          (if j.1 + 1 < L then neumannBarrier H0 r L (j.1 + 1) else neumannBarrier H0 r L (L - 1)) := by
        by_cases hlt : j.1 + 1 < L
        · simp only [hlt, ↓reduceDIte, ↓reduceIte]
          exact ih ⟨j.1 + 1, hlt⟩
        · simp only [hlt, ↓reduceDIte, ↓reduceIte]
          exact ih ⟨L - 1, by omega⟩
      have hmudt : (0 : Rat) ≤ mu_eff * dt := Rat.mul_nonneg hmu hdt
      have hm1 := Rat.mul_le_mul_of_nonneg_left hmid hdiag
      have hm2 := Rat.mul_le_mul_of_nonneg_left (by grind :
          H k ⟨j.1 - 1, by omega⟩ + (if h : j.1 + 1 < L then H k ⟨j.1 + 1, h⟩ else H k ⟨L - 1, by omega⟩) ≤
          neumannBarrier H0 r L (j.1 - 1) +
            (if j.1 + 1 < L then neumannBarrier H0 r L (j.1 + 1) else neumannBarrier H0 r L (L - 1))) hmudt
      have hinv := neumannBarrier_step_invariant hH0 hr hdt hbar hj1 j.2
      grind

/-- Exact exit-row (`j = L - 1`) specialization of `neumannBarrier`:
    `neumannBarrier H0 r L (L - 1) = H0 * (ratPow r (L - 1) + ratPow r L) / (1 + ratPow r (2 * L - 1))`. -/
theorem neumannBarrier_exit (H0 r : Rat) {L : Nat} (hL : 1 ≤ L) :
    neumannBarrier H0 r L (L - 1) =
      H0 * (ratPow r (L - 1) + ratPow r L) / (1 + ratPow r (2 * L - 1)) := by
  unfold neumannBarrier
  have h1 : 2 * L - 1 - (L - 1) = L := by omega
  rw [h1]


/-! ## Part 4: Antisymmetric Row Vector `ℓ²` & `ℓ∞` Exact Algebraic Bounds -/

/-- Exact sum over `Fin w` by structural recursion. -/
def sumFin : (w : Nat) → (Fin w → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.succ_pos n⟩ + sumFin n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem sumFin_nonneg : ∀ (w : Nat) (f : Fin w → Rat),
    (∀ i, (0 : Rat) ≤ f i) → (0 : Rat) ≤ sumFin w f := by
  intro w
  induction w with
  | zero => intro _ _; simp [sumFin]
  | succ n ih =>
    intro f hf
    simp only [sumFin]
    have h0 := hf ⟨0, Nat.succ_pos n⟩
    have hr := ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) (fun i => hf _)
    grind

theorem sumFin_le_const : ∀ (w : Nat) (f : Fin w → Rat) (c : Rat),
    (∀ i, f i ≤ c) → sumFin w f ≤ (w : Rat) * c := by
  intro w
  induction w with
  | zero => intro _ _ _; simp [sumFin]
  | succ n ih =>
    intro f c hf
    simp only [sumFin]
    have h0 := hf ⟨0, Nat.succ_pos n⟩
    have hr := ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) c (fun i => hf _)
    have hcast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
    rw [hcast]; grind

theorem sumFin_single_le : ∀ (w : Nat) (f : Fin w → Rat),
    (∀ i, (0 : Rat) ≤ f i) → ∀ i : Fin w, f i ≤ sumFin w f := by
  intro w
  induction w with
  | zero => intro _ _ i; exact Fin.elim0 i
  | succ n ih =>
    intro f hf i
    simp only [sumFin]
    cases hi : i.1 with
    | zero =>
      have heq : i = ⟨0, Nat.succ_pos n⟩ := Fin.ext hi
      rw [heq]
      have hr := sumFin_nonneg n (fun j => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) (fun j => hf _)
      grind
    | succ m =>
      have hm : m < n := by omega
      have heq : i = ⟨m + 1, Nat.succ_lt_succ hm⟩ := Fin.ext hi
      rw [heq]
      have h0 := hf ⟨0, Nat.succ_pos n⟩
      have hr := ih (fun j => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) (fun j => hf _) ⟨m, hm⟩
      grind

theorem sumFin_pair_le : ∀ (w : Nat) (f : Fin w → Rat),
    (∀ i, (0 : Rat) ≤ f i) → ∀ i j : Fin w, i ≠ j → f i + f j ≤ sumFin w f := by
  intro w
  induction w with
  | zero => intro _ _ i; exact Fin.elim0 i
  | succ n ih =>
    intro f hf i j hij
    simp only [sumFin]
    cases hi : i.1 with
    | zero =>
      have hi0 : i = ⟨0, Nat.succ_pos n⟩ := Fin.ext hi
      cases hj : j.1 with
      | zero =>
        exfalso; apply hij; exact Fin.ext (by omega)
      | succ m =>
        have hm : m < n := by omega
        have hj' : j = ⟨m + 1, Nat.succ_lt_succ hm⟩ := Fin.ext hj
        rw [hi0, hj']
        have hr := sumFin_single_le n (fun k => f ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) (fun k => hf _) ⟨m, hm⟩
        grind
    | succ m1 =>
      have hm1 : m1 < n := by omega
      have hi' : i = ⟨m1 + 1, Nat.succ_lt_succ hm1⟩ := Fin.ext hi
      cases hj : j.1 with
      | zero =>
        have hj0 : j = ⟨0, Nat.succ_pos n⟩ := Fin.ext hj
        rw [hi', hj0]
        have hr := sumFin_single_le n (fun k => f ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) (fun k => hf _) ⟨m1, hm1⟩
        grind
      | succ m2 =>
        have hm2 : m2 < n := by omega
        have hj' : j = ⟨m2 + 1, Nat.succ_lt_succ hm2⟩ := Fin.ext hj
        have hne : (⟨m1, hm1⟩ : Fin n) ≠ ⟨m2, hm2⟩ := fun h => by
          apply hij; apply Fin.ext; injection h with hm; rw [hi, hj, hm]
        rw [hi', hj']
        have h0 := hf ⟨0, Nat.succ_pos n⟩
        have hr := ih (fun k => f ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) (fun k => hf _) ⟨m1, hm1⟩ ⟨m2, hm2⟩ hne
        grind

/-- Exact mirror reflection index `revIdx i = w - 1 - i`. -/
def revIdx {w : Nat} (i : Fin w) : Fin w :=
  ⟨w - 1 - i.1, by omega⟩

theorem revIdx_involutive {w : Nat} (i : Fin w) : revIdx (revIdx i) = i := by
  apply Fin.ext; simp only [revIdx]; omega

/-- Antisymmetric lateral component `v(i) = (a(i) - a(w - 1 - i)) / 2`. -/
def antisym {w : Nat} (a : Fin w → Rat) (i : Fin w) : Rat :=
  (a i - a (revIdx i)) / 2

theorem antisym_odd {w : Nat} (a : Fin w → Rat) (i : Fin w) :
    antisym a (revIdx i) = -(antisym a i) := by
  unfold antisym
  rw [revIdx_involutive]
  grind

/-- Exact squared `ℓ²` row norm `‖v‖₂² = ∑_i v(i)²`. -/
def rowNormSq (w : Nat) (v : Fin w → Rat) : Rat :=
  sumFin w (fun i => v i * v i)

/-- **Entrance Bound**: For ANY `a : Fin w → Rat` with `0 ≤ a i ≤ 1`,
    `‖v‖₂² ≤ w / 4` (i.e., `‖v‖₂ ≤ √w / 2`). -/
theorem antisym_entrance_normSq_le {w : Nat} (a : Fin w → Rat)
    (h0 : ∀ i, (0 : Rat) ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    rowNormSq w (antisym a) ≤ (w : Rat) / 4 := by
  unfold rowNormSq
  have hpt : ∀ i : Fin w, antisym a i * antisym a i ≤ (1 / 4 : Rat) := by
    intro i
    unfold antisym
    have ha0 := h0 i; have ha1 := h1 i
    have hb0 := h0 (revIdx i); have hb1 := h1 (revIdx i)
    have hdiff_lo : -(1 : Rat) ≤ a i - a (revIdx i) := by grind
    have hdiff_hi : a i - a (revIdx i) ≤ 1 := by grind
    have hsq : (a i - a (revIdx i)) * (a i - a (revIdx i)) ≤ 1 := by
      have hprod := Rat.mul_nonneg (by grind : (0 : Rat) ≤ 1 - (a i - a (revIdx i)))
        (by grind : (0 : Rat) ≤ 1 + (a i - a (revIdx i)))
      grind
    grind
  have hsum := sumFin_le_const w (fun i => antisym a i * antisym a i) (1 / 4 : Rat) hpt
  grind

/-- **Pointwise Asymmetry vs. `ℓ²` Norm Bound (Zero Square Roots)**:
    For EVERY row vector `a : Fin w → Rat` and EVERY index `i : Fin w`,
    `(a i - a (revIdx i))² ≤ 2 * ‖v‖₂²` (i.e., `|a(x) - a(-x)| ≤ √2 · ‖v‖₂`). -/
theorem antisym_linf_sq_le_two_normSq {w : Nat} (a : Fin w → Rat) (i : Fin w) :
    (a i - a (revIdx i)) * (a i - a (revIdx i)) ≤ 2 * rowNormSq w (antisym a) := by
  unfold rowNormSq
  have hnn : ∀ k : Fin w, (0 : Rat) ≤ antisym a k * antisym a k := fun k => by
    cases @Rat.le_total (antisym a k) 0 with
    | inl hle =>
      have := Rat.mul_nonneg (by grind : (0 : Rat) ≤ -(antisym a k)) (by grind : (0 : Rat) ≤ -(antisym a k))
      grind
    | inr hge => exact Rat.mul_nonneg hge hge
  by_cases heq : i = revIdx i
  · have hzero : a i - a (revIdx i) = 0 := by rw [← heq]; grind
    rw [hzero]
    have hs := sumFin_nonneg w (fun k => antisym a k * antisym a k) hnn
    grind
  · have hpair := sumFin_pair_le w (fun k => antisym a k * antisym a k) hnn i (revIdx i) heq
    have hodd := antisym_odd a i
    have hsq : antisym a (revIdx i) * antisym a (revIdx i) = antisym a i * antisym a i := by
      rw [hodd]; grind
    have h4 : (a i - a (revIdx i)) * (a i - a (revIdx i)) = 4 * (antisym a i * antisym a i) := by
      unfold antisym; grind
    grind


/-! ## Part 5: Exact Rational Certificates for M-15 `w = 25` (`h_0`, `L = 107`) & `w = 50` (`h/2`, `L = 214`) -/

/-- Alternating Taylor lower bound for `sin(x)` on `(0, π/2]`:
    `sinLoPoly x = x - x^3/6 + x^5/120 - x^7/5040`. -/
def sinLoPoly (x : Rat) : Rat :=
  x - x * x * x / 6 + x * x * x * x * x / 120 - x * x * x * x * x * x * x / 5040

/-- Helper: `ratPow (p / q) n = (p^n : Rat) / (q^n : Rat)` for `p, q : Nat`. -/
theorem ratPow_nat_div (p q : Nat) (n : Nat) :
    ratPow ((p : Rat) / (q : Rat)) n = ((p ^ n : Nat) : Rat) / ((q ^ n : Nat) : Rat) := by
  induction n with
  | zero => simp [ratPow]; grind
  | succ k ih =>
    simp only [ratPow, ih, Nat.pow_succ]
    have hp : ((p ^ k * p : Nat) : Rat) = ((p ^ k : Nat) : Rat) * (p : Rat) := by grind
    have hq : ((q ^ k * q : Nat) : Rat) = ((q ^ k : Nat) : Rat) * (q : Rat) := by grind
    rw [hp, hq]; grind

/-- Pure-integer exit bound helper: lifts a kernel-decided `Nat` inequality
    `w * (2 * p^(L-1) * q^L)^2 * ubDen^2 < 2 * (q^(2L-1) + p^(2L-1))^2 * ubNum^2`
    into `(w / 2) * (2 * (p/q)^(L-1) / (1 + (p/q)^(2L-1)))^2 < (ubNum / ubDen)^2`. -/
theorem exit_linf_sq_from_nat {w L p q ubNum ubDen : Nat}
    (hL : 1 ≤ L) (hq : 0 < q) (hubD : 0 < ubDen)
    (hnat : w * (2 * p ^ (L - 1) * q ^ L) ^ 2 * ubDen ^ 2 <
            2 * (q ^ (2 * L - 1) + p ^ (2 * L - 1)) ^ 2 * ubNum ^ 2) :
    let r : Rat := (p : Rat) / (q : Rat)
    let ratio := (2 * ratPow r (L - 1)) / (1 + ratPow r (2 * L - 1))
    ((w : Rat) / 2) * (ratio * ratio) < ((ubNum : Rat) / (ubDen : Rat)) * ((ubNum : Rat) / (ubDen : Rat)) := by
  intro r ratio
  have hq_pos : (0 : Rat) < (q : Rat) := natCast_pos_rat hq
  have hubD_pos : (0 : Rat) < (ubDen : Rat) := natCast_pos_rat hubD
  have hqL_pos : (0 : Rat) < ((q ^ L : Nat) : Rat) := natCast_pos_rat (Nat.pow_pos hq)
  have hq2L_pos : (0 : Rat) < ((q ^ (2 * L - 1) : Nat) : Rat) := natCast_pos_rat (Nat.pow_pos hq)
  have hp2L_nn : (0 : Rat) ≤ ((p ^ (2 * L - 1) : Nat) : Rat) := by
    have : (0 : Int) ≤ ((p ^ (2 * L - 1) : Nat) : Int) := Int.natCast_nonneg _
    have h' := intCast_rat_le_iff.mpr this
    rw [intCast_natCast_rat] at h'; exact h'
  have hratio_eq : ratio = ((2 * p ^ (L - 1) * q ^ L : Nat) : Rat) /
      ((q ^ (2 * L - 1) + p ^ (2 * L - 1) : Nat) : Rat) := by
    simp only [ratio, r, ratPow_nat_div]
    have hpow_split : q ^ (2 * L - 1) = q ^ (L - 1) * q ^ L := by
      rw [← Nat.pow_add]; congr 1; omega
    have hq_cast : ((q ^ (2 * L - 1) : Nat) : Rat) = ((q ^ (L - 1) : Nat) : Rat) * ((q ^ L : Nat) : Rat) := by
      rw [hpow_split]; grind
    have hnum_cast : ((2 * p ^ (L - 1) * q ^ L : Nat) : Rat) =
        2 * ((p ^ (L - 1) : Nat) : Rat) * ((q ^ L : Nat) : Rat) := by grind
    have hden_cast : ((q ^ (2 * L - 1) + p ^ (2 * L - 1) : Nat) : Rat) =
        ((q ^ (2 * L - 1) : Nat) : Rat) + ((p ^ (2 * L - 1) : Nat) : Rat) := by grind
    have hqLm1_pos : (0 : Rat) < ((q ^ (L - 1) : Nat) : Rat) := natCast_pos_rat (Nat.pow_pos hq)
    have hne1 : ((q ^ (L - 1) : Nat) : Rat) ≠ 0 := by grind
    have hne2 : ((q ^ (2 * L - 1) : Nat) : Rat) ≠ 0 := by grind
    have hne3 : ((q ^ (2 * L - 1) : Nat) : Rat) + ((p ^ (2 * L - 1) : Nat) : Rat) ≠ 0 := by grind
    rw [hnum_cast, hden_cast, hq_cast]
    grind
  rw [hratio_eq]
  have hlt_rat : ((w * (2 * p ^ (L - 1) * q ^ L) ^ 2 * ubDen ^ 2 : Nat) : Rat) <
      ((2 * (q ^ (2 * L - 1) + p ^ (2 * L - 1)) ^ 2 * ubNum ^ 2 : Nat) : Rat) := by
    have hInt : ((w * (2 * p ^ (L - 1) * q ^ L) ^ 2 * ubDen ^ 2 : Nat) : Int) <
        ((2 * (q ^ (2 * L - 1) + p ^ (2 * L - 1)) ^ 2 * ubNum ^ 2 : Nat) : Int) := by omega
    have hR := intCast_rat_lt_iff.mpr hInt
    rw [intCast_natCast_rat, intCast_natCast_rat] at hR
    exact hR
  let A : Rat := ((2 * p ^ (L - 1) * q ^ L : Nat) : Rat)
  let B : Rat := ((q ^ (2 * L - 1) + p ^ (2 * L - 1) : Nat) : Rat)
  have hB_pos : (0 : Rat) < B := by
    have hpos : 0 < q ^ (2 * L - 1) + p ^ (2 * L - 1) := Nat.add_pos_left (Nat.pow_pos hq) _
    exact natCast_pos_rat hpos
  have hlt_exp : (w : Rat) * (A * A) * ((ubDen : Rat) * (ubDen : Rat)) <
      2 * (B * B) * ((ubNum : Rat) * (ubNum : Rat)) := by
    have hL_cast : ((w * (2 * p ^ (L - 1) * q ^ L) ^ 2 * ubDen ^ 2 : Nat) : Rat) =
        (w : Rat) * (A * A) * ((ubDen : Rat) * (ubDen : Rat)) := by
      simp only [A, Nat.pow_two]; grind
    have hR_cast : ((2 * (q ^ (2 * L - 1) + p ^ (2 * L - 1)) ^ 2 * ubNum ^ 2 : Nat) : Rat) =
        2 * (B * B) * ((ubNum : Rat) * (ubNum : Rat)) := by
      simp only [B, Nat.pow_two]; grind
    rw [hL_cast, hR_cast] at hlt_rat
    exact hlt_rat
  have hden_pos : (0 : Rat) < 2 * (B * B) * ((ubDen : Rat) * (ubDen : Rat)) :=
    Rat.mul_pos (Rat.mul_pos (by grind) (Rat.mul_pos hB_pos hB_pos)) (Rat.mul_pos hubD_pos hubD_pos)
  have hinv_pos : (0 : Rat) < 1 / (2 * (B * B) * ((ubDen : Rat) * (ubDen : Rat))) :=
    rat_one_div_pos hden_pos
  have hmul := Rat.mul_pos (by grind : (0 : Rat) < 2 * (B * B) * ((ubNum : Rat) * (ubNum : Rat)) -
      (w : Rat) * (A * A) * ((ubDen : Rat) * (ubDen : Rat))) hinv_pos
  have hB_ne : B ≠ 0 := by grind
  have hD_ne : (ubDen : Rat) ≠ 0 := by grind
  have hre : (2 * (B * B) * ((ubNum : Rat) * (ubNum : Rat)) -
      (w : Rat) * (A * A) * ((ubDen : Rat) * (ubDen : Rat))) *
      (1 / (2 * (B * B) * ((ubDen : Rat) * (ubDen : Rat)))) =
      ((ubNum : Rat) / (ubDen : Rat)) * ((ubNum : Rat) / (ubDen : Rat)) -
      ((w : Rat) / 2) * ((A / B) * (A / B)) := by
    grind
  rw [hre] at hmul
  change ((w : Rat) / 2) * ((A / B) * (A / B)) < _
  grind

/-- Helper: exact conservative upper bound on `neumannBarrier H0 r L (L - 1)` for `0 < r ≤ 1`:
    since `r^L ≤ r^(L-1)`, `neumannBarrier H0 r L (L - 1) ≤ H0 * (2 * r^(L-1)) / (1 + r^(2L-1))`. -/
theorem neumannBarrier_exit_le {H0 r : Rat} (hH0 : (0 : Rat) ≤ H0) (hr0 : (0 : Rat) < r) (hr1 : r ≤ 1)
    {L : Nat} (hL : 1 ≤ L) :
    neumannBarrier H0 r L (L - 1) ≤
      H0 * (2 * ratPow r (L - 1)) / (1 + ratPow r (2 * L - 1)) := by
  unfold neumannBarrier
  have h1 : 2 * L - 1 - (L - 1) = L := by omega
  rw [h1]
  have hp_eq : ratPow r L = r * ratPow r (L - 1) := by
    cases hL_eq : L with | zero => omega | succ m => simp [ratPow]
  rw [hp_eq]
  have hp_pos := ratPow_pos hr0 (L - 1)
  have hr_le : r * ratPow r (L - 1) ≤ ratPow r (L - 1) := by
    have := Rat.mul_le_mul_of_nonneg_right hr1 (by grind : (0 : Rat) ≤ ratPow r (L - 1))
    grind
  have hnum_le : H0 * (ratPow r (L - 1) + r * ratPow r (L - 1)) ≤ H0 * (2 * ratPow r (L - 1)) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) hH0
  have hden_pos : (0 : Rat) < 1 + ratPow r (2 * L - 1) := by
    have := ratPow_pos hr0 (2 * L - 1); grind
  have hinv_nn : (0 : Rat) ≤ 1 / (1 + ratPow r (2 * L - 1)) := by
    cases @Rat.le_total (1 / (1 + ratPow r (2 * L - 1))) 0 with
    | inl hle =>
      exfalso
      have hm := Rat.mul_le_mul_of_nonneg_left hle (by grind : (0 : Rat) ≤ 1 + ratPow r (2 * L - 1))
      have hne : 1 + ratPow r (2 * L - 1) ≠ 0 := by grind
      grind
    | inr hge => exact hge
  have hm := Rat.mul_le_mul_of_nonneg_right hnum_le hinv_nn
  grind

/-- **Certificate 1 (`h_0 = 1/143`, `dt = 1/4`, `w = 25`, `L = 107`, `5pt`)**:
    Exact row-diagonal SPD margin `69239/100000 > 0`, global SPD margin `> 0`,
    damping `gamma_lo > 1908/1000000 > 0`, spatial barrier `r_ub = 907952/1000000`
    satisfying `mu * (r_ub + 1/r_ub - 2) ≤ gamma_lo`, and exit pointwise squared asymmetry
    strictly `< (2537 / 10000000)^2` (cross-checked `< 2.537e-4`). -/
theorem m27_h0_w25_5pt_cert :
    let hInv : Rat := 143
    let dt : Rat := 1 / 4
    let mu : Rat := diffDa * hInv * hInv
    let sLo : Rat := sinLoPoly (piLoRat / 50)
    let gammaLo : Rat := diffDa * (4 * hInv * hInv * sLo * sLo) - fPrimeMax
    let rUb : Rat := (907952 : Rat) / 1000000
    (1 - 6 * mu * dt + dt * fPrimeMin = (69239 / 100000 : Rat)) ∧
    ((0 : Rat) < 1 - 8 * mu * dt + dt * fPrimeMin) ∧
    ((1908 / 1000000 : Rat) < gammaLo) ∧
    (mu * (rUb + 1 / rUb - 2) ≤ gammaLo) ∧
    (((25 : Rat) / 2) *
      (((2 * ratPow rUb 106) / (1 + ratPow rUb 213)) *
       ((2 * ratPow rUb 106) / (1 + ratPow rUb 213))) <
      ((2537 : Rat) / 10000000) * ((2537 : Rat) / 10000000)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMax sinLoPoly piLoRat; grind
  · unfold diffDa fPrimeMax sinLoPoly piLoRat; grind
  · exact exit_linf_sq_from_nat (w := 25) (L := 107) (p := 907952) (q := 1000000)
      (ubNum := 2537) (ubDen := 10000000) (by omega) (by omega) (by omega) (by decide)

/-- **Certificate 2 (`h_0 = 1/143`, `dt = 1/4`, `w = 25`, `L = 107`, `9pt`)**:
    Exact row-diagonal SPD margin `114083/150000 > 0`, global SPD margin `> 0`,
    effective coupling `mu_9 = mu * (1 - 2/3 * sLo^2)`, spatial barrier `r_ub = 907837/1000000`
    satisfying `mu_9 * (r_ub + 1/r_ub - 2) ≤ gamma_lo`, and exit pointwise squared asymmetry
    strictly `< (2503 / 10000000)^2` (cross-checked `< 2.503e-4`). -/
theorem m27_h0_w25_9pt_cert :
    let hInv : Rat := 143
    let dt : Rat := 1 / 4
    let mu : Rat := diffDa * hInv * hInv
    let sLo : Rat := sinLoPoly (piLoRat / 50)
    let gammaLo : Rat := diffDa * (4 * hInv * hInv * sLo * sLo) - fPrimeMax
    let mu9Hi : Rat := mu * (1 - (2 / 3 : Rat) * sLo * sLo)
    let rUb : Rat := (907837 : Rat) / 1000000
    (1 - (14 / 3 : Rat) * mu * dt + dt * fPrimeMin = (114083 / 150000 : Rat)) ∧
    ((0 : Rat) < 1 - (16 / 3 : Rat) * mu * dt + dt * fPrimeMin) ∧
    (mu9Hi * (rUb + 1 / rUb - 2) ≤ gammaLo) ∧
    (((25 : Rat) / 2) *
      (((2 * ratPow rUb 106) / (1 + ratPow rUb 213)) *
       ((2 * ratPow rUb 106) / (1 + ratPow rUb 213))) <
      ((2503 : Rat) / 10000000) * ((2503 : Rat) / 10000000)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMax sinLoPoly piLoRat; grind
  · exact exit_linf_sq_from_nat (w := 25) (L := 107) (p := 907837) (q := 1000000)
      (ubNum := 2503) (ubDen := 10000000) (by omega) (by omega) (by omega) (by decide)

set_option exponentiation.threshold 512 in
/-- **Certificate 3 (`h/2 = 1/286`, `dt = 1/16`, `w = 50`, `L = 214`, `5pt`)**:
    Refined fine-grid certificate matching the same physical width `25 * h_0 = 50 * (h_0/2)`,
    with `r_ub = 952814/1000000` and exit pointwise squared asymmetry `< (3379 / 10000000)^2`. -/
theorem m27_h2_w50_5pt_cert :
    let hInv : Rat := 286
    let dt : Rat := 1 / 16
    let mu : Rat := diffDa * hInv * hInv
    let sLo : Rat := sinLoPoly (piLoRat / 100)
    let gammaLo : Rat := diffDa * (4 * hInv * hInv * sLo * sLo) - fPrimeMax
    let rUb : Rat := (952814 : Rat) / 1000000
    ((0 : Rat) < 1 - 6 * mu * dt + dt * fPrimeMin) ∧
    ((0 : Rat) < 1 - 8 * mu * dt + dt * fPrimeMin) ∧
    (mu * (rUb + 1 / rUb - 2) ≤ gammaLo) ∧
    (((50 : Rat) / 2) *
      (((2 * ratPow rUb 213) / (1 + ratPow rUb 427)) *
       ((2 * ratPow rUb 213) / (1 + ratPow rUb 427))) <
      ((3379 : Rat) / 10000000) * ((3379 : Rat) / 10000000)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMax sinLoPoly piLoRat; grind
  · exact exit_linf_sq_from_nat (w := 50) (L := 214) (p := 952814) (q := 1000000)
      (ubNum := 3379) (ubDen := 10000000) (by omega) (by omega) (by omega) (by decide)

set_option exponentiation.threshold 512 in
/-- **Certificate 4 (`h/2 = 1/286`, `dt = 1/16`, `w = 50`, `L = 214`, `9pt`)**:
    Refined fine-grid `9pt` certificate with `r_ub = 952799/1000000` and exit pointwise squared
    asymmetry `< (3368 / 10000000)^2`. -/
theorem m27_h2_w50_9pt_cert :
    let hInv : Rat := 286
    let dt : Rat := 1 / 16
    let mu : Rat := diffDa * hInv * hInv
    let sLo : Rat := sinLoPoly (piLoRat / 100)
    let gammaLo : Rat := diffDa * (4 * hInv * hInv * sLo * sLo) - fPrimeMax
    let mu9Hi : Rat := mu * (1 - (2 / 3 : Rat) * sLo * sLo)
    let rUb : Rat := (952799 : Rat) / 1000000
    ((0 : Rat) < 1 - (14 / 3 : Rat) * mu * dt + dt * fPrimeMin) ∧
    ((0 : Rat) < 1 - (16 / 3 : Rat) * mu * dt + dt * fPrimeMin) ∧
    (mu9Hi * (rUb + 1 / rUb - 2) ≤ gammaLo) ∧
    (((50 : Rat) / 2) *
      (((2 * ratPow rUb 213) / (1 + ratPow rUb 427)) *
       ((2 * ratPow rUb 213) / (1 + ratPow rUb 427))) <
      ((3368 : Rat) / 10000000) * ((3368 : Rat) / 10000000)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMin; grind
  · unfold diffDa fPrimeMax sinLoPoly piLoRat; grind
  · exact exit_linf_sq_from_nat (w := 50) (L := 214) (p := 952799) (q := 1000000)
      (ubNum := 3368) (ubDen := 10000000) (by omega) (by omega) (by omega) (by decide)

end M27SymmetryContraction
