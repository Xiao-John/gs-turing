/-
  Lean 4 Formalization of the Confirmed Theorem (M-41):
    "Discrete Ginzburg–Landau Lyapunov Descent, Negative-Energy Reset Obstruction,
     Exact Four-Grid Descent Constants, and Uniform Fuel Depletion from Threshold Witness"
  Source verdict:
    coordination/confirm/2026-11-23_m41_scalar_reset/VERDICT.md
    coordination/confirm/2026-11-23_m41_scalar_reset/REPORT.md
  Zero external dependencies (pure Lean 4.36.0 core `Init` + native `Rat`, zero `sorry`).
-/

namespace M41ScalarReset

/-! ## Part 1: Exact `Rat` Properties of the Bistable Nagumo Reaction and Potential -/

/-- Exact bistable Nagumo reaction `g(w) = (1/200) * w * (1 - w) * (w - 3/10)`. -/
def nagumo (w : Rat) : Rat :=
  (1 / 200 : Rat) * w * (1 - w) * (w - 3 / 10)

/-- Exact antiderivative potential `G(w) = ∫_0^w g(s) ds = -w^4/800 + 13 w^3/6000 - 3 w^2/4000`. -/
def potential (w : Rat) : Rat :=
  -(1 / 800 : Rat) * w * w * w * w
  + (13 / 6000 : Rat) * w * w * w
  - (3 / 4000 : Rat) * w * w

/-- Exact global Lipschitz constant of `g` on `[0, 1]`: `L_g = 7/2000 = 7 * λ / 10`. -/
def L_g : Rat := 7 / 2000

private theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases @Rat.le_total (0 : Rat) x with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := by grind
    have hprod := Rat.mul_nonneg hneg hneg
    grind

theorem nagumo_zero : nagumo 0 = 0 := by unfold nagumo; grind
theorem nagumo_one : nagumo 1 = 0 := by unfold nagumo; grind
theorem potential_zero : potential 0 = 0 := by unfold potential; grind
theorem potential_one : potential 1 = (1 / 6000 : Rat) := by unfold potential; grind
theorem potential_theta : potential (3 / 10 : Rat) = -(153 / 8000000 : Rat) := by
  unfold potential; grind

/-- Lemma 1.1 (Global Quadratic Upper Bound on `G`):
    For EVERY `w : Rat`, `G(w) ≤ (L_g / 2) * w^2 = (7/4000) * w^2`. -/
theorem potential_le_quadratic (w : Rat) :
    potential w ≤ (L_g / 2) * (w * w) := by
  have hid : (L_g / 2) * (w * w) - potential w =
      (1 / 24000 : Rat) * (w * w) * (30 * ((w - 13 / 15 : Rat) * (w - 13 / 15 : Rat)) + 562 / 15) := by
    unfold potential L_g
    grind
  have hw2 : (0 : Rat) ≤ w * w := rat_sq_nonneg w
  have hsq : (0 : Rat) ≤ (w - 13 / 15 : Rat) * (w - 13 / 15 : Rat) := rat_sq_nonneg (w - 13 / 15)
  have hpos1 : (0 : Rat) ≤ (1 / 24000 : Rat) * (w * w) := Rat.mul_nonneg (by grind) hw2
  have hpos2 : (0 : Rat) ≤ 30 * ((w - 13 / 15 : Rat) * (w - 13 / 15 : Rat)) + 562 / 15 := by grind
  have hprod := Rat.mul_nonneg hpos1 hpos2
  rw [← hid] at hprod
  grind

/-- Lemma 1.2 (Exact Algebraic Taylor Lower Bound for `G`, Zero Calculus):
    For all `u v : Rat` in `[0, 1]`,
      `G(v) - G(u) ≥ g(u) * (v - u) - (L_g / 2) * (v - u)^2`. -/
theorem potential_taylor_lower_bound {u v : Rat}
    (hu0 : (0 : Rat) ≤ u) (hu1 : u ≤ 1) (hv0 : (0 : Rat) ≤ v) (hv1 : v ≤ 1) :
    nagumo u * (v - u) - (L_g / 2) * ((v - u) * (v - u)) ≤ potential v - potential u := by
  have hid :
      potential v - potential u - nagumo u * (v - u) + (L_g / 2) * ((v - u) * (v - u)) =
      (1 / 24000 : Rat) * ((v - u) * (v - u)) *
        (90 * (1 - u) * u + 30 * (1 - v) * v +
         30 * (1 - u) * v + 30 * (1 - v) * u +
         16 * (1 - u) + 8 * (1 - v)) := by
    unfold potential nagumo L_g
    grind
  have hsq : (0 : Rat) ≤ (v - u) * (v - u) := rat_sq_nonneg (v - u)
  have h1u : (0 : Rat) ≤ 1 - u := by grind
  have h1v : (0 : Rat) ≤ 1 - v := by grind
  have t1 : (0 : Rat) ≤ 90 * (1 - u) * u := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1u) hu0
  have t2 : (0 : Rat) ≤ 30 * (1 - v) * v := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1v) hv0
  have t3 : (0 : Rat) ≤ 30 * (1 - u) * v := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1u) hv0
  have t4 : (0 : Rat) ≤ 30 * (1 - v) * u := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1v) hu0
  have hpoly : (0 : Rat) ≤
      90 * (1 - u) * u + 30 * (1 - v) * v +
      30 * (1 - u) * v + 30 * (1 - v) * u +
      16 * (1 - u) + 8 * (1 - v) := by grind
  have hcoeff : (0 : Rat) ≤ (1 / 24000 : Rat) * ((v - u) * (v - u)) :=
    Rat.mul_nonneg (by grind) hsq
  have hprod := Rat.mul_nonneg hcoeff hpoly
  rw [← hid] at hprod
  grind

/-- Lemma 1.3 (Exact Algebraic Lower Slope Bound on `g`):
    For all `0 ≤ a ≤ b ≤ 1`, `-L_g * (b - a) ≤ g(b) - g(a)`. -/
theorem nagumo_diff_lower_bound {a b : Rat}
    (ha0 : (0 : Rat) ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    -L_g * (b - a) ≤ nagumo b - nagumo a := by
  have hid :
      nagumo b - nagumo a + L_g * (b - a) =
      (b - a) * ((1 / 2000 : Rat) *
        (10 * (1 - a) * a + 10 * (1 - b) * b +
         5 * (1 - a) * b + 5 * (1 - b) * a +
         2 * ((1 - a) + (1 - b)))) := by
    unfold nagumo L_g
    grind
  have ha1 : a ≤ 1 := by grind
  have hb0 : (0 : Rat) ≤ b := by grind
  have hba : (0 : Rat) ≤ b - a := by grind
  have h1a : (0 : Rat) ≤ 1 - a := by grind
  have h1b : (0 : Rat) ≤ 1 - b := by grind
  have t1 : (0 : Rat) ≤ 10 * (1 - a) * a := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1a) ha0
  have t2 : (0 : Rat) ≤ 10 * (1 - b) * b := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1b) hb0
  have t3 : (0 : Rat) ≤ 5 * (1 - a) * b := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1a) hb0
  have t4 : (0 : Rat) ≤ 5 * (1 - b) * a := Rat.mul_nonneg (Rat.mul_nonneg (by grind) h1b) ha0
  have hpoly : (0 : Rat) ≤
      (1 / 2000 : Rat) *
      (10 * (1 - a) * a + 10 * (1 - b) * b +
       5 * (1 - a) * b + 5 * (1 - b) * a +
       2 * ((1 - a) + (1 - b))) :=
    Rat.mul_nonneg (by grind) (by grind)
  have hprod := Rat.mul_nonneg hba hpoly
  rw [← hid] at hprod
  grind


/-! ## Part 2: Finite Sums over `List` & Symmetric-Graph Discrete Ginzburg–Landau Energy -/

def sumList {α : Type} (xs : List α) (f : α → Rat) : Rat :=
  xs.foldl (fun acc x => acc + f x) 0

private theorem sumList_foldl_shift {α : Type} (xs : List α) (f : α → Rat) (init : Rat) :
    xs.foldl (fun acc x => acc + f x) init = init + sumList xs f := by
  unfold sumList
  induction xs generalizing init with
  | nil => simp only [List.foldl]; grind
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (init + f x), ih (0 + f x)]
    grind

theorem sumList_nil {α : Type} (f : α → Rat) : sumList ([] : List α) f = 0 := rfl

theorem sumList_cons {α : Type} (x : α) (xs : List α) (f : α → Rat) :
    sumList (x :: xs) f = f x + sumList xs f := by
  unfold sumList
  simp only [List.foldl]
  rw [sumList_foldl_shift]
  unfold sumList
  grind

theorem sumList_add {α : Type} (xs : List α) (f g : α → Rat) :
    sumList xs (fun x => f x + g x) = sumList xs f + sumList xs g := by
  induction xs with
  | nil => simp only [sumList_nil]; grind
  | cons x xs ih => rw [sumList_cons, sumList_cons, sumList_cons, ih]; grind

theorem sumList_sub {α : Type} (xs : List α) (f g : α → Rat) :
    sumList xs (fun x => f x - g x) = sumList xs f - sumList xs g := by
  induction xs with
  | nil => simp only [sumList_nil]; grind
  | cons x xs ih => rw [sumList_cons, sumList_cons, sumList_cons, ih]; grind

theorem sumList_mul_left {α : Type} (xs : List α) (c : Rat) (f : α → Rat) :
    sumList xs (fun x => c * f x) = c * sumList xs f := by
  induction xs with
  | nil => simp only [sumList_nil]; grind
  | cons x xs ih => rw [sumList_cons, sumList_cons, ih]; grind

theorem sumList_le {α : Type} (xs : List α) {f g : α → Rat}
    (h : ∀ x ∈ xs, f x ≤ g x) :
    sumList xs f ≤ sumList xs g := by
  induction xs with
  | nil => simp only [sumList_nil]; grind
  | cons x xs ih =>
    rw [sumList_cons, sumList_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    grind

theorem sumList_nonneg {α : Type} (xs : List α) {f : α → Rat}
    (h : ∀ x ∈ xs, (0 : Rat) ≤ f x) :
    (0 : Rat) ≤ sumList xs f := by
  have h0 : sumList xs (fun _ => (0 : Rat)) = 0 := by
    clear h
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [sumList_cons, ih]; grind
  rw [← h0]
  exact sumList_le xs h

theorem sumList_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Rat) :
    sumList xs (fun x => sumList ys (fun y => f x y)) =
    sumList ys (fun y => sumList xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    rw [sumList_nil]
    induction ys with
    | nil => rfl
    | cons y ys ihy => rw [sumList_cons, sumList_nil, ← ihy]; grind
  | cons x xs ih =>
    rw [sumList_cons, ih]
    have hstep :
        sumList ys (fun y => f x y) + sumList ys (fun y => sumList xs (fun x' => f x' y)) =
        sumList ys (fun y => f x y + sumList xs (fun x' => f x' y)) :=
      (sumList_add ys _ _).symm
    rw [hstep]
    have heq : (fun y => f x y + sumList xs (fun x' => f x' y)) =
        (fun y => sumList (x :: xs) (fun x' => f x' y)) := by
      funext y
      exact (sumList_cons x xs (fun x' => f x' y)).symm
    rw [heq]

/-- A finite symmetric non-negative weighted graph reaction-diffusion system over `Fin N`.
    `W i j = W j i ≥ 0` are the discrete Laplacian weights (already including `1/h^2`),
    with weighted degree bound `∑_j W i j ≤ dMax`. -/
structure SymGraphNagumo (N : Nat) where
  D : Rat
  hD_nonneg : (0 : Rat) ≤ D
  dt : Rat
  hdt_pos : (0 : Rat) < dt
  W : Fin N → Fin N → Rat
  hW_nonneg : ∀ i j, (0 : Rat) ≤ W i j
  hW_sym : ∀ i j, W i j = W j i
  dMax : Rat
  hdMax : ∀ i, sumList (List.finRange N) (fun j => W i j) ≤ dMax
  /-- Diagonal monotonicity condition: `1 - dt * (D * dMax + L_g) ≥ 0`. -/
  hdiag_nonneg : (0 : Rat) ≤ 1 - dt * (D * dMax + L_g)

def SymGraphNagumo.nodes {N : Nat} (_ : SymGraphNagumo N) : List (Fin N) :=
  List.finRange N

/-- Discrete gradient-flow right-hand side `rhs(w)_i = D * ∑_j W_{ij} (w_j - w_i) + g(w_i)`. -/
def SymGraphNagumo.rhs {N : Nat} (S : SymGraphNagumo N) (w : Fin N → Rat) (i : Fin N) : Rat :=
  S.D * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)) + nagumo (w i)

/-- Explicit Euler update `F(w)_i = w_i + dt * rhs(w)_i`. -/
def SymGraphNagumo.step {N : Nat} (S : SymGraphNagumo N) (w : Fin N → Rat) (i : Fin N) : Rat :=
  w i + S.dt * S.rhs w i

/-- Discrete Ginzburg–Landau Lyapunov energy:
    `E_h(w) = (D/4) * ∑_{i,j} W_{ij} (w_j - w_i)^2 - ∑_i G(w_i)`. -/
def SymGraphNagumo.energy {N : Nat} (S : SymGraphNagumo N) (w : Fin N → Rat) : Rat :=
  (S.D / 4) * sumList (List.finRange N) (fun i =>
    sumList (List.finRange N) (fun j => S.W i j * ((w j - w i) * (w j - w i))))
  - sumList (List.finRange N) (fun i => potential (w i))

/-- Discrete Euclidean norm squared `‖v‖_2^2 = ∑_i v_i^2`. -/
def normSq {N : Nat} (v : Fin N → Rat) : Rat :=
  sumList (List.finRange N) (fun i => v i * v i)

/-- Exact discrete Lyapunov descent coefficient `α = 1 - (dt/2) * (2*D*dMax + L_g)`. -/
def SymGraphNagumo.alpha {N : Nat} (S : SymGraphNagumo N) : Rat :=
  1 - (S.dt / 2) * (2 * S.D * S.dMax + L_g)

/-- Theorem 2.1 (Order Preservation & `[0, 1]^N` Box Invariance of `F`). -/
theorem SymGraphNagumo.step_monotone {N : Nat} (S : SymGraphNagumo N)
    {a b : Fin N → Rat}
    (ha0 : ∀ i, (0 : Rat) ≤ a i) (hab : ∀ i, a i ≤ b i) (hb1 : ∀ i, b i ≤ 1) (i : Fin N) :
    S.step a i ≤ S.step b i := by
  unfold SymGraphNagumo.step SymGraphNagumo.rhs
  have hdt0 : (0 : Rat) ≤ S.dt := by have := S.hdt_pos; grind
  -- Split `∑_j W_{ij} (a_j - a_i) = (∑_j W_{ij} a_j) - (∑_j W_{ij}) * a_i`
  have hsplit : ∀ (v : Fin N → Rat),
      sumList (List.finRange N) (fun j => S.W i j * (v j - v i)) =
      sumList (List.finRange N) (fun j => S.W i j * v j) -
      sumList (List.finRange N) (fun j => S.W i j) * v i := by
    intro v
    have h1 : (fun j => S.W i j * (v j - v i)) = (fun j => S.W i j * v j - S.W i j * v i) := by
      funext j; grind
    rw [h1, sumList_sub]
    have h2 : (fun j => S.W i j * v i) = (fun j => v i * S.W i j) := by funext j; grind
    rw [h2, sumList_mul_left]
    grind
  rw [hsplit a, hsplit b]
  have hnb :
      sumList (List.finRange N) (fun j => S.W i j * a j) ≤
      sumList (List.finRange N) (fun j => S.W i j * b j) := by
    apply sumList_le
    intro j _
    exact Rat.mul_le_mul_of_nonneg_left (hab j) (S.hW_nonneg i j)
  have hDnb :
      S.dt * S.D * sumList (List.finRange N) (fun j => S.W i j * a j) ≤
      S.dt * S.D * sumList (List.finRange N) (fun j => S.W i j * b j) :=
    Rat.mul_le_mul_of_nonneg_left hnb (Rat.mul_nonneg hdt0 S.hD_nonneg)
  have hnag : -L_g * (b i - a i) ≤ nagumo (b i) - nagumo (a i) :=
    nagumo_diff_lower_bound (ha0 i) (hab i) (hb1 i)
  have hdtnag : S.dt * (-L_g * (b i - a i)) ≤ S.dt * (nagumo (b i) - nagumo (a i)) :=
    Rat.mul_le_mul_of_nonneg_left hnag hdt0
  have hd_le := S.hdMax i
  have hdiag := S.hdiag_nonneg
  have hD0 := S.hD_nonneg
  have hdeg : S.dt * S.D * sumList (List.finRange N) (fun j => S.W i j) ≤ S.dt * S.D * S.dMax :=
    Rat.mul_le_mul_of_nonneg_left hd_le (Rat.mul_nonneg hdt0 hD0)
  have hba : (0 : Rat) ≤ b i - a i := by have := hab i; grind
  have hcenter : (0 : Rat) ≤
      (1 - S.dt * S.D * sumList (List.finRange N) (fun j => S.W i j) - S.dt * L_g) * (b i - a i) :=
    Rat.mul_nonneg (by grind) hba
  grind

theorem SymGraphNagumo.step_const {N : Nat} (S : SymGraphNagumo N) (c : Rat) (i : Fin N) :
    S.step (fun _ => c) i = c + S.dt * nagumo c := by
  unfold SymGraphNagumo.step SymGraphNagumo.rhs
  have h0 : sumList (List.finRange N) (fun j => S.W i j * (c - c)) = 0 := by
    have hz : (fun j => S.W i j * (c - c)) = (fun _ => (0 : Rat)) := by funext j; grind
    rw [hz]
    induction (List.finRange N) with
    | nil => rfl
    | cons _ xs ih => rw [sumList_cons, ih]; grind
  rw [h0]; grind

theorem SymGraphNagumo.step_in_box {N : Nat} (S : SymGraphNagumo N)
    {w : Fin N → Rat} (h0 : ∀ i, (0 : Rat) ≤ w i) (h1 : ∀ i, w i ≤ 1) (i : Fin N) :
    (0 : Rat) ≤ S.step w i ∧ S.step w i ≤ 1 := by
  have hz : S.step (fun _ => 0) i = 0 := by rw [S.step_const 0 i, nagumo_zero]; grind
  have ho : S.step (fun _ => 1) i = 1 := by rw [S.step_const 1 i, nagumo_one]; grind
  have hlo : S.step (fun _ => 0) i ≤ S.step w i :=
    S.step_monotone (fun _ => by grind) h0 h1 i
  have hhi : S.step w i ≤ S.step (fun _ => 1) i :=
    S.step_monotone h0 h1 (fun _ => by grind) i
  rw [hz] at hlo
  rw [ho] at hhi
  exact ⟨hlo, hhi⟩

/-- Exact Symmetric Quadratic-Form Expansion:
    `∑_{i,j} W_{ij} ((w_j + δ_j) - (w_i + δ_i))^2 - ∑_{i,j} W_{ij} (w_j - w_i)^2
     = -4 ∑_i δ_i (∑_j W_{ij} (w_j - w_i)) + ∑_{i,j} W_{ij} (δ_j - δ_i)^2`. -/
private theorem sym_quad_expansion {N : Nat} (S : SymGraphNagumo N) (w δ : Fin N → Rat) :
    sumList (List.finRange N) (fun i =>
      sumList (List.finRange N) (fun j => S.W i j * (((w j + δ j) - (w i + δ i)) * ((w j + δ j) - (w i + δ i)))))
    - sumList (List.finRange N) (fun i =>
      sumList (List.finRange N) (fun j => S.W i j * ((w j - w i) * (w j - w i))))
    =
    -4 * sumList (List.finRange N) (fun i =>
      δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))
    + sumList (List.finRange N) (fun i =>
      sumList (List.finRange N) (fun j => S.W i j * ((δ j - δ i) * (δ j - δ i)))) := by
  rw [← sumList_sub]
  have hinner :
      (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * (((w j + δ j) - (w i + δ i)) * ((w j + δ j) - (w i + δ i))))
        - sumList (List.finRange N) (fun j => S.W i j * ((w j - w i) * (w j - w i))))
      =
      (fun i =>
        sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * (δ j - δ i))
        + sumList (List.finRange N) (fun j => S.W i j * ((δ j - δ i) * (δ j - δ i)))) := by
    funext i
    rw [← sumList_sub, ← sumList_add]
    have hpt :
        (fun j => S.W i j * (((w j + δ j) - (w i + δ i)) * ((w j + δ j) - (w i + δ i)))
                  - S.W i j * ((w j - w i) * (w j - w i)))
        =
        (fun j => 2 * S.W i j * (w j - w i) * (δ j - δ i) + S.W i j * ((δ j - δ i) * (δ j - δ i))) := by
      funext j; grind
    rw [hpt]
  rw [hinner, sumList_add]
  have hcross :
      sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * (δ j - δ i))) =
      -4 * sumList (List.finRange N) (fun i =>
        δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i))) := by
    have hsplit :
        (fun i => sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * (δ j - δ i))) =
        (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * δ j)
          - sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * δ i)) := by
      funext i
      rw [← sumList_sub]
      have : (fun j => 2 * S.W i j * (w j - w i) * (δ j - δ i)) =
          (fun j => 2 * S.W i j * (w j - w i) * δ j - 2 * S.W i j * (w j - w i) * δ i) := by
        funext j; grind
      rw [this]
    rw [hsplit, sumList_sub]
    rw [sumList_swap (List.finRange N) (List.finRange N) (fun i j => 2 * S.W i j * (w j - w i) * δ j)]
    have hsym_eq :
        sumList (List.finRange N) (fun j =>
          sumList (List.finRange N) (fun i => 2 * S.W i j * (w j - w i) * δ j)) =
        -sumList (List.finRange N) (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * δ i)) := by
      have hneg :
          (fun j => sumList (List.finRange N) (fun i => 2 * S.W i j * (w j - w i) * δ j)) =
          (fun j => (-1 : Rat) * sumList (List.finRange N) (fun i => 2 * S.W j i * (w i - w j) * δ j)) := by
        funext j
        rw [← sumList_mul_left]
        have : (fun i => 2 * S.W i j * (w j - w i) * δ j) =
            (fun i => (-1 : Rat) * (2 * S.W j i * (w i - w j) * δ j)) := by
          funext i
          rw [S.hW_sym i j]
          grind
        rw [this]
      rw [hneg, sumList_mul_left]
      grind
    rw [hsym_eq]
    have hpull :
        sumList (List.finRange N) (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * δ i)) =
        2 * sumList (List.finRange N) (fun i =>
          δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i))) := by
      rw [← sumList_mul_left]
      have : (fun i => sumList (List.finRange N) (fun j => 2 * S.W i j * (w j - w i) * δ i)) =
          (fun i => 2 * (δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))) := by
        funext i
        rw [← sumList_mul_left, ← sumList_mul_left]
        have : (fun j => 2 * S.W i j * (w j - w i) * δ i) =
            (fun j => 2 * (δ i * (S.W i j * (w j - w i)))) := by
          funext j; grind
        rw [this]
      rw [this]
    rw [hpull]
    grind
  rw [hcross]

/-- Quadratic-form upper bound `∑_{i,j} W_{ij} (δ_j - δ_i)^2 ≤ 4 * dMax * ∑_i δ_i^2`. -/
private theorem sym_quad_upper_bound {N : Nat} (S : SymGraphNagumo N) (δ : Fin N → Rat) :
    sumList (List.finRange N) (fun i =>
      sumList (List.finRange N) (fun j => S.W i j * ((δ j - δ i) * (δ j - δ i)))) ≤
    4 * S.dMax * normSq δ := by
  have hle1 :
      sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * ((δ j - δ i) * (δ j - δ i)))) ≤
      sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * (2 * (δ j * δ j) + 2 * (δ i * δ i)))) := by
    apply sumList_le; intro i _
    apply sumList_le; intro j _
    have hsq : (0 : Rat) ≤ (δ j + δ i) * (δ j + δ i) := rat_sq_nonneg (δ j + δ i)
    have hineq : (δ j - δ i) * (δ j - δ i) ≤ 2 * (δ j * δ j) + 2 * (δ i * δ i) := by grind
    exact Rat.mul_le_mul_of_nonneg_left hineq (S.hW_nonneg i j)
  have hsplit :
      sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * (2 * (δ j * δ j) + 2 * (δ i * δ i)))) =
      4 * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i)) := by
    have h1 :
        (fun i => sumList (List.finRange N) (fun j => S.W i j * (2 * (δ j * δ j) + 2 * (δ i * δ i)))) =
        (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (δ j * δ j))
          + sumList (List.finRange N) (fun j => 2 * S.W i j * (δ i * δ i))) := by
      funext i
      rw [← sumList_add]
      have : (fun j => S.W i j * (2 * (δ j * δ j) + 2 * (δ i * δ i))) =
          (fun j => 2 * S.W i j * (δ j * δ j) + 2 * S.W i j * (δ i * δ i)) := by
        funext j; grind
      rw [this]
    rw [h1, sumList_add]
    rw [sumList_swap (List.finRange N) (List.finRange N) (fun i j => 2 * S.W i j * (δ j * δ j))]
    have hsym_eq :
        sumList (List.finRange N) (fun j =>
          sumList (List.finRange N) (fun i => 2 * S.W i j * (δ j * δ j))) =
        sumList (List.finRange N) (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (δ i * δ i))) := by
      have : (fun j => sumList (List.finRange N) (fun i => 2 * S.W i j * (δ j * δ j))) =
          (fun j => sumList (List.finRange N) (fun i => 2 * S.W j i * (δ j * δ j))) := by
        funext j
        have : (fun i => 2 * S.W i j * (δ j * δ j)) = (fun i => 2 * S.W j i * (δ j * δ j)) := by
          funext i; rw [S.hW_sym i j]
        rw [this]
      rw [this]
    rw [hsym_eq]
    have hpull :
        sumList (List.finRange N) (fun i =>
          sumList (List.finRange N) (fun j => 2 * S.W i j * (δ i * δ i))) =
        2 * sumList (List.finRange N) (fun i =>
          sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i)) := by
      rw [← sumList_mul_left]
      have : (fun i => sumList (List.finRange N) (fun j => 2 * S.W i j * (δ i * δ i))) =
          (fun i => 2 * (sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i))) := by
        funext i
        have hcomm :
            2 * (sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i)) =
            (2 * (δ i * δ i)) * sumList (List.finRange N) (fun j => S.W i j) := by grind
        rw [hcomm, ← sumList_mul_left]
        have : (fun j => 2 * S.W i j * (δ i * δ i)) =
            (fun j => (2 * (δ i * δ i)) * S.W i j) := by funext j; grind
        rw [this]
      rw [this]
    rw [hpull]
    grind
  have hle2 :
      4 * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i)) ≤
      4 * S.dMax * normSq δ := by
    unfold normSq
    have h4 : 4 * S.dMax * sumList (List.finRange N) (fun i => δ i * δ i) =
        4 * sumList (List.finRange N) (fun i => S.dMax * (δ i * δ i)) := by
      rw [sumList_mul_left]; grind
    rw [h4]
    have hsum :
        sumList (List.finRange N) (fun i => sumList (List.finRange N) (fun j => S.W i j) * (δ i * δ i)) ≤
        sumList (List.finRange N) (fun i => S.dMax * (δ i * δ i)) := by
      apply sumList_le; intro i _
      have hsq : (0 : Rat) ≤ δ i * δ i := rat_sq_nonneg (δ i)
      have hm := Rat.mul_le_mul_of_nonneg_left (S.hdMax i) hsq
      grind
    grind
  grind

/-- Main Theorem 2.2 (Exact Discrete Ginzburg–Landau Lyapunov Descent, `VERDICT.md` §二):
    For every state `w` in `[0, 1]^N`,
      `E_h(F(w)) - E_h(w) ≤ -dt * α * ‖rhs(w)‖_2^2`,
    where `α = 1 - (dt/2) * (2*D*dMax + L_g)`. -/
theorem SymGraphNagumo.energy_step_descent {N : Nat} (S : SymGraphNagumo N)
    {w : Fin N → Rat} (h0 : ∀ i, (0 : Rat) ≤ w i) (h1 : ∀ i, w i ≤ 1) :
    S.energy (S.step w) - S.energy w ≤ -S.dt * S.alpha * normSq (S.rhs w) := by
  let δ : Fin N → Rat := fun i => S.dt * S.rhs w i
  have hstep_eq : S.step w = fun i => w i + δ i := rfl
  have hbox : ∀ i, (0 : Rat) ≤ w i + δ i ∧ w i + δ i ≤ 1 := fun i => S.step_in_box h0 h1 i
  have hqexp := sym_quad_expansion S w δ
  have hqub := sym_quad_upper_bound S δ
  have hpot :
      sumList (List.finRange N) (fun i => nagumo (w i) * δ i - (L_g / 2) * (δ i * δ i)) ≤
      sumList (List.finRange N) (fun i => potential (w i + δ i) - potential (w i)) := by
    apply sumList_le; intro i _
    have hp := potential_taylor_lower_bound (h0 i) (h1 i) (hbox i).1 (hbox i).2
    have hdiff : (w i + δ i) - w i = δ i := by grind
    rw [hdiff] at hp
    exact hp
  have hlin :
      S.D * sumList (List.finRange N) (fun i =>
        δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))
      + sumList (List.finRange N) (fun i => nagumo (w i) * δ i) =
      S.dt * normSq (S.rhs w) := by
    rw [← sumList_mul_left, ← sumList_add]
    unfold normSq
    rw [← sumList_mul_left]
    have heq :
        (fun i => S.D * (δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))
                  + nagumo (w i) * δ i) =
        (fun i => S.dt * (S.rhs w i * S.rhs w i)) := by
      funext i
      show S.D * ((S.dt * S.rhs w i) * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))
           + nagumo (w i) * (S.dt * S.rhs w i) = S.dt * (S.rhs w i * S.rhs w i)
      unfold SymGraphNagumo.rhs
      grind
    rw [heq]
  have hnormδ : normSq δ = (S.dt * S.dt) * normSq (S.rhs w) := by
    unfold normSq
    rw [← sumList_mul_left]
    have : (fun i => δ i * δ i) = (fun i => (S.dt * S.dt) * (S.rhs w i * S.rhs w i)) := by
      funext i
      show (S.dt * S.rhs w i) * (S.dt * S.rhs w i) = (S.dt * S.dt) * (S.rhs w i * S.rhs w i)
      grind
    rw [this]
  have hD4 : (0 : Rat) ≤ S.D / 4 := by have := S.hD_nonneg; grind
  have hqub_scaled := Rat.mul_le_mul_of_nonneg_left hqub hD4
  unfold SymGraphNagumo.energy SymGraphNagumo.alpha
  rw [hstep_eq]
  rw [sumList_sub] at hpot
  rw [sumList_sub] at hpot
  have hLpull :
      sumList (List.finRange N) (fun i => (L_g / 2) * (δ i * δ i)) =
      (L_g / 2) * normSq δ := sumList_mul_left (List.finRange N) (L_g / 2) (fun i => δ i * δ i)
  rw [hLpull, hnormδ] at hpot
  rw [hnormδ] at hqub_scaled
  have hqdiff :
      (S.D / 4) * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * (((w j + δ j) - (w i + δ i)) * ((w j + δ j) - (w i + δ i)))))
      - (S.D / 4) * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * ((w j - w i) * (w j - w i))))
      =
      -S.D * sumList (List.finRange N) (fun i =>
        δ i * sumList (List.finRange N) (fun j => S.W i j * (w j - w i)))
      + (S.D / 4) * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * ((δ j - δ i) * (δ j - δ i)))) := by
    have hmul := congrArg (fun z => (S.D / 4) * z) hqexp
    grind
  grind


/-! ## Part 3: Negative-Energy Reset Obstruction (Discrete Version of `VERDICT.md` §一) -/

/-- Lemma 3.1: For any `w : Fin N → Rat`, `E_h(w) ≥ -(L_g / 2) * ‖w‖_2^2`. -/
theorem SymGraphNagumo.energy_lower_bound {N : Nat} (S : SymGraphNagumo N) (w : Fin N → Rat) :
    -(L_g / 2) * normSq w ≤ S.energy w := by
  unfold SymGraphNagumo.energy normSq
  have hquad_nonneg :
      (0 : Rat) ≤ (S.D / 4) * sumList (List.finRange N) (fun i =>
        sumList (List.finRange N) (fun j => S.W i j * ((w j - w i) * (w j - w i)))) := by
    apply Rat.mul_nonneg (by have := S.hD_nonneg; grind)
    apply sumList_nonneg; intro i _
    apply sumList_nonneg; intro j _
    exact Rat.mul_nonneg (S.hW_nonneg i j) (rat_sq_nonneg (w j - w i))
  have hpot_ub :
      sumList (List.finRange N) (fun i => potential (w i)) ≤
      (L_g / 2) * sumList (List.finRange N) (fun i => w i * w i) := by
    rw [← sumList_mul_left]
    apply sumList_le; intro i _
    exact potential_le_quadratic (w i)
  grind

/-- Main Theorem 3.2 (Discrete Negative-Energy Reset Obstruction, `VERDICT.md` §一–§二):
    Let `w : Nat → Fin N → Rat` be any autonomous exact Euler orbit in `[0, 1]^N` with `α ≥ 0`.
    If at some step `n0`, `E_h(w n0) ≤ -δ` with `δ > 0`, then for ALL subsequent steps `k : Nat`:
      1. `E_h(w (n0 + k)) ≤ -δ`, and
      2. `‖w (n0 + k)‖_2^2 ≥ 2 * δ / L_g > 0`
    (precluding both exact reset to `0` and asymptotic convergence to `0`). -/
theorem m41_negative_energy_reset_obstruction {N : Nat} (S : SymGraphNagumo N)
    (halpha : (0 : Rat) ≤ S.alpha)
    (w : Nat → Fin N → Rat)
    (hinit0 : ∀ i, (0 : Rat) ≤ w 0 i)
    (hinit1 : ∀ i, w 0 i ≤ 1)
    (hstep : ∀ n, w (n + 1) = S.step (w n))
    (n0 : Nat) (δ : Rat) (hδ : (0 : Rat) < δ)
    (hnegE : S.energy (w n0) ≤ -δ) :
    ∀ k : Nat,
      S.energy (w (n0 + k)) ≤ -δ ∧
      (2 * δ) / L_g ≤ normSq (w (n0 + k)) ∧
      (0 : Rat) < normSq (w (n0 + k)) := by
  have hbox_all : ∀ n i, (0 : Rat) ≤ w n i ∧ w n i ≤ 1 := by
    intro n
    induction n with
    | zero => intro i; exact ⟨hinit0 i, hinit1 i⟩
    | succ n ih =>
      intro i
      rw [hstep n]
      exact S.step_in_box (fun j => (ih j).1) (fun j => (ih j).2) i
  have henergy_le : ∀ k : Nat, S.energy (w (n0 + k)) ≤ -δ := by
    intro k
    induction k with
    | zero => simpa using hnegE
    | succ k ih =>
      have hdesc := S.energy_step_descent
        (fun j => (hbox_all (n0 + k) j).1)
        (fun j => (hbox_all (n0 + k) j).2)
      have hnorm_nonneg : (0 : Rat) ≤ normSq (S.rhs (w (n0 + k))) := by
        unfold normSq
        apply sumList_nonneg; intro i _
        exact rat_sq_nonneg (S.rhs (w (n0 + k)) i)
      have hdt0 : (0 : Rat) ≤ S.dt := by have := S.hdt_pos; grind
      have hdrop : (0 : Rat) ≤ S.dt * S.alpha * normSq (S.rhs (w (n0 + k))) :=
        Rat.mul_nonneg (Rat.mul_nonneg hdt0 halpha) hnorm_nonneg
      have hnext : w (n0 + (k + 1)) = S.step (w (n0 + k)) := by
        have : n0 + (k + 1) = (n0 + k) + 1 := by omega
        rw [this, hstep]
      rw [hnext]
      grind
  intro k
  have hEk := henergy_le k
  have hlb := S.energy_lower_bound (w (n0 + k))
  have hdist : (2 * δ) / L_g ≤ normSq (w (n0 + k)) := by
    unfold L_g at hlb ⊢
    grind
  have hpos : (0 : Rat) < normSq (w (n0 + k)) := by
    unfold L_g at hdist
    grind
  exact ⟨hEk, hdist, hpos⟩


/-! ## Part 4: Exact Four-Grid Descent & Monotonicity Constants (`REPORT.md` Table) -/

/-- Exact rational verification of all four `(stencil, h, dt)` configurations in `REPORT.md`:
    - `5pt, h=1/143, dt=1/4`:  diag_lb = `158927/200000`, `α = 318029/400000 > 0`
    - `9pt, h=1/143, dt=1/4`:  diag_lb = `49723/60000`,   `α = 198997/240000 > 0`
    - `5pt, h=1/286, dt=1/16`: diag_lb = `636233/800000`, `α = 1272641/1600000 > 0`
    - `9pt, h=1/286, dt=1/16`: diag_lb = `398099/480000`, `α = 796303/960000 > 0` -/
theorem m41_four_grid_exact_constants :
    let D : Rat := 1 / 100000
    let d5_h0 : Rat := 4 * (143 * 143)
    let d9_h0 : Rat := (10 / 3) * (143 * 143)
    let d5_h2 : Rat := 4 * (286 * 286)
    let d9_h2 : Rat := (10 / 3) * (286 * 286)
    let dt0 : Rat := 1 / 4
    let dt2 : Rat := 1 / 16
    (1 - dt0 * (D * d5_h0 + L_g) = 158927 / 200000) ∧
    (1 - (dt0 / 2) * (2 * D * d5_h0 + L_g) = 318029 / 400000) ∧
    (1 - dt0 * (D * d9_h0 + L_g) = 49723 / 60000) ∧
    (1 - (dt0 / 2) * (2 * D * d9_h0 + L_g) = 198997 / 240000) ∧
    (1 - dt2 * (D * d5_h2 + L_g) = 636233 / 800000) ∧
    (1 - (dt2 / 2) * (2 * D * d5_h2 + L_g) = 1272641 / 1600000) ∧
    (1 - dt2 * (D * d9_h2 + L_g) = 398099 / 480000) ∧
    (1 - (dt2 / 2) * (2 * D * d9_h2 + L_g) = 796303 / 960000) := by
  unfold L_g
  grind


/-! ## Part 5: Threshold Witness → Uniform Fuel Depletion `w → 1` (`r → 0`, `VERDICT.md` §三) -/

/-- Spatially constant 1-step orbit `z_{j+1} = z_j + dt * g(z_j)`. -/
def scalarStep (dt z : Rat) : Rat :=
  z + dt * nagumo z

def scalarOrbit (dt z0 : Rat) : Nat → Rat
  | 0 => z0
  | j + 1 => scalarStep dt (scalarOrbit dt z0 j)

/-- For `0 < dt ≤ 1/4` and `3/10 < z < 1`, `z < scalarStep dt z < 1`. -/
theorem scalarStep_strict_inc_lt_one {dt z : Rat}
    (hdt0 : (0 : Rat) < dt) (hdt1 : dt ≤ 1 / 4)
    (hz_lo : (3 / 10 : Rat) < z) (hz_hi : z < 1) :
    z < scalarStep dt z ∧ scalarStep dt z < 1 := by
  unfold scalarStep nagumo
  have h1z : (0 : Rat) < 1 - z := by grind
  have hzt : (0 : Rat) < z - 3 / 10 := by grind
  have hz0 : (0 : Rat) < z := by grind
  have hprod_pos : (0 : Rat) < (1 / 200 : Rat) * z * (1 - z) * (z - 3 / 10) :=
    Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by grind) hz0) h1z) hzt
  have hinc : (0 : Rat) < dt * ((1 / 200 : Rat) * z * (1 - z) * (z - 3 / 10)) :=
    Rat.mul_pos hdt0 hprod_pos
  have hz_le1 : z ≤ 1 := by grind
  have hzt_le1 : z - 3 / 10 ≤ 1 := by grind
  have hmul1 : z * (z - 3 / 10) ≤ 1 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hzt_le1 (by grind : (0 : Rat) ≤ z)
    grind
  have hcoeff : dt * ((1 / 200 : Rat) * (z * (z - 3 / 10))) ≤ 1 / 800 := by
    have hm1 : (1 / 200 : Rat) * (z * (z - 3 / 10)) ≤ 1 / 200 := by
      have hm := Rat.mul_le_mul_of_nonneg_left hmul1 (by grind : (0 : Rat) ≤ (1 / 200 : Rat))
      grind
    have hm2 : dt * ((1 / 200 : Rat) * (z * (z - 3 / 10))) ≤ (1 / 4 : Rat) * (1 / 200 : Rat) := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hm1 (by grind : (0 : Rat) ≤ dt)
      have h2 := Rat.mul_le_mul_of_nonneg_left hdt1 (by grind : (0 : Rat) ≤ (1 / 200 : Rat))
      grind
    grind
  have hstep_ub : dt * ((1 / 200 : Rat) * z * (1 - z) * (z - 3 / 10)) ≤ (1 / 800 : Rat) * (1 - z) := by
    have heq : dt * ((1 / 200 : Rat) * z * (1 - z) * (z - 3 / 10)) =
        (1 - z) * (dt * ((1 / 200 : Rat) * (z * (z - 3 / 10)))) := by grind
    rw [heq]
    have hm := Rat.mul_le_mul_of_nonneg_left hcoeff (by grind : (0 : Rat) ≤ 1 - z)
    grind
  grind

/-- Monotonicity and boundedness of `scalarOrbit`. -/
theorem scalarOrbit_bounds {dt z0 : Rat}
    (hdt0 : (0 : Rat) < dt) (hdt1 : dt ≤ 1 / 4)
    (hz_lo : (3 / 10 : Rat) < z0) (hz_hi : z0 < 1) :
    ∀ j : Nat, z0 ≤ scalarOrbit dt z0 j ∧ scalarOrbit dt z0 j < 1 ∧
      scalarOrbit dt z0 j < scalarOrbit dt z0 (j + 1) := by
  intro j
  induction j with
  | zero =>
    simp only [scalarOrbit]
    have hs := scalarStep_strict_inc_lt_one hdt0 hdt1 hz_lo hz_hi
    exact ⟨by grind, hz_hi, hs.1⟩
  | succ j ih =>
    have hcur_lo : (3 / 10 : Rat) < scalarOrbit dt z0 (j + 1) := by grind
    have hcur_hi : scalarOrbit dt z0 (j + 1) < 1 := by
      simp only [scalarOrbit]
      exact (scalarStep_strict_inc_lt_one hdt0 hdt1 (by grind) ih.2.1).2
    have hnext := scalarStep_strict_inc_lt_one hdt0 hdt1 hcur_lo hcur_hi
    exact ⟨by grind, hcur_hi, hnext.1⟩

/-- Helper: `scalarOrbit` is monotone in step index. -/
theorem scalarOrbit_mono {dt z0 : Rat}
    (hdt0 : (0 : Rat) < dt) (hdt1 : dt ≤ 1 / 4)
    (hz_lo : (3 / 10 : Rat) < z0) (hz_hi : z0 < 1)
    {j₁ j₂ : Nat} (hle : j₁ ≤ j₂) :
    scalarOrbit dt z0 j₁ ≤ scalarOrbit dt z0 j₂ := by
  induction hle with
  | refl => grind
  | @step m _ ih =>
    have hinc := (scalarOrbit_bounds hdt0 hdt1 hz_lo hz_hi m).2.2
    grind

/-- Exact Rational Convergence Theorem (`scalarOrbit → 1`):
    For any `0 < dt ≤ 1/4`, `3/10 < z0 < 1`, and any tolerance `ε > 0`,
    there exists `M : Nat` such that for all `j ≥ M`, `1 - ε < scalarOrbit dt z0 j < 1`. -/
theorem scalarOrbit_approaches_one {dt z0 ε : Rat}
    (hdt0 : (0 : Rat) < dt) (hdt1 : dt ≤ 1 / 4)
    (hz_lo : (3 / 10 : Rat) < z0) (hz_hi : z0 < 1) (hε : (0 : Rat) < ε) :
    ∃ M : Nat, ∀ j : Nat, M ≤ j → 1 - ε < scalarOrbit dt z0 j ∧ scalarOrbit dt z0 j < 1 := by
  let c : Rat := dt * ((1 / 200 : Rat) * z0 * ε * (z0 - 3 / 10))
  have hc_pos : (0 : Rat) < c :=
    Rat.mul_pos hdt0
      (Rat.mul_pos
        (Rat.mul_pos
          (Rat.mul_pos (by grind : (0 : Rat) < 1 / 200) (by grind : (0 : Rat) < z0))
          hε)
        (by grind : (0 : Rat) < z0 - 3 / 10))
  have hstep_lb : ∀ j, scalarOrbit dt z0 j ≤ 1 - ε →
      scalarOrbit dt z0 j + c ≤ scalarOrbit dt z0 (j + 1) := by
    intro j hj
    have hjb := scalarOrbit_bounds hdt0 hdt1 hz_lo hz_hi j
    show scalarOrbit dt z0 j + c ≤ scalarOrbit dt z0 j + dt * nagumo (scalarOrbit dt z0 j)
    have h1 : (1 / 200 : Rat) * z0 ≤ (1 / 200 : Rat) * scalarOrbit dt z0 j := by grind
    have h2 : ε ≤ 1 - scalarOrbit dt z0 j := by grind
    have h3 : z0 - 3 / 10 ≤ scalarOrbit dt z0 j - 3 / 10 := by grind
    have hm1 : (1 / 200 : Rat) * z0 * ε ≤ (1 / 200 : Rat) * scalarOrbit dt z0 j * (1 - scalarOrbit dt z0 j) := by
      have ha := Rat.mul_le_mul_of_nonneg_left h2 (by grind : (0 : Rat) ≤ (1 / 200 : Rat) * z0)
      have hb := Rat.mul_le_mul_of_nonneg_left h1 (by grind : (0 : Rat) ≤ 1 - scalarOrbit dt z0 j)
      grind
    have hm2 : (1 / 200 : Rat) * z0 * ε * (z0 - 3 / 10) ≤ nagumo (scalarOrbit dt z0 j) := by
      unfold nagumo
      have ha := Rat.mul_le_mul_of_nonneg_left h3
        (Rat.mul_nonneg (by grind : (0 : Rat) ≤ (1 / 200 : Rat) * z0) (by grind : (0 : Rat) ≤ ε))
      have hb := Rat.mul_le_mul_of_nonneg_left hm1
        (by grind : (0 : Rat) ≤ scalarOrbit dt z0 j - 3 / 10)
      grind
    have hm3 := Rat.mul_le_mul_of_nonneg_left hm2 (by grind : (0 : Rat) ≤ dt)
    grind
  -- Archimedean step count `M = ceil(1/c).toNat + 1` so `M * c > 1`
  let M : Nat := (1 / c).ceil.toNat + 1
  have hMc : (1 : Rat) < (M : Rat) * c := by
    have hceil : (1 / c : Rat) ≤ ((1 / c).ceil : Rat) := @Rat.le_ceil (1 / c)
    have htoNat : ((1 / c).ceil : Rat) ≤ ((1 / c).ceil.toNat : Rat) := by
      have hcast_eq : ∀ n : Nat, ((n : Int) : Rat) = (n : Rat) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          have h1 : (((n + 1 : Nat) : Int) : Rat) = ((n : Int) : Rat) + 1 := by grind
          have h2 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
          rw [h1, h2, ih]
      have hnat_nn : ∀ n : Nat, (0 : Rat) ≤ (n : Rat) := by
        intro n
        induction n with
        | zero => grind
        | succ n ih =>
          have h2 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
          grind
      cases h : (1 / c).ceil with
      | ofNat n =>
        simp only [Int.toNat]
        have := hcast_eq n
        grind
      | negSucc n =>
        simp only [Int.toNat]
        have heq := hcast_eq n
        have hnn := hnat_nn n
        grind
    have hM_gt : (1 / c : Rat) < (M : Rat) := by
      have hM_eq : (M : Rat) = ((1 / c).ceil.toNat : Rat) + 1 := by grind
      grind
    have hdiff_pos : (0 : Rat) < ((M : Rat) - 1 / c) * c :=
      Rat.mul_pos (by grind) hc_pos
    have hcancel : (1 / c) * c = 1 := by
      have hne : c ≠ 0 := by grind
      grind
    grind
  have hM_crossed : 1 - ε < scalarOrbit dt z0 M := by
    cases @Rat.le_total (scalarOrbit dt z0 M) (1 - ε) with
    | inr hgt =>
      by_cases heq : scalarOrbit dt z0 M = 1 - ε
      · exfalso
        have hlin : ∀ k, k ≤ M → z0 + (k : Rat) * c ≤ scalarOrbit dt z0 k := by
          intro k hk
          induction k with
          | zero => simp only [scalarOrbit]; grind
          | succ k ih =>
            have hk_le : k ≤ M := by omega
            have hprev := ih hk_le
            have hle_M := scalarOrbit_mono hdt0 hdt1 hz_lo hz_hi hk_le
            have hinc := hstep_lb k (by grind)
            have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
            rw [hcast]
            grind
        have hM_lb := hlin M (Nat.le_refl M)
        have hM_ub := (scalarOrbit_bounds hdt0 hdt1 hz_lo hz_hi M).2.1
        grind
      · grind
    | inl hle =>
      exfalso
      have hlin : ∀ k, k ≤ M → z0 + (k : Rat) * c ≤ scalarOrbit dt z0 k := by
        intro k hk
        induction k with
        | zero => simp only [scalarOrbit]; grind
        | succ k ih =>
          have hk_le : k ≤ M := by omega
          have hprev := ih hk_le
          have hle_M := scalarOrbit_mono hdt0 hdt1 hz_lo hz_hi hk_le
          have hinc := hstep_lb k (by grind)
          have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
          rw [hcast]
          grind
      have hM_lb := hlin M (Nat.le_refl M)
      have hM_ub := (scalarOrbit_bounds hdt0 hdt1 hz_lo hz_hi M).2.1
      grind
  refine ⟨M, fun j hj => ?_⟩
  have hmono := scalarOrbit_mono hdt0 hdt1 hz_lo hz_hi hj
  have hub := (scalarOrbit_bounds hdt0 hdt1 hz_lo hz_hi j).2.1
  exact ⟨by grind, hub⟩

/-- Main Theorem 5.1 (Uniform Fuel Depletion `w → 1`, i.e., `r = 1 - w → 0`, `VERDICT.md` §三):
    Suppose an autonomous exact Euler orbit `w` of `S` (with `dt ≤ 1/4`) in `[0, 1]^N`
    satisfies a uniform threshold lower bound `∀ i, z0 ≤ w n0 i` at some step `n0`
    with `3/10 < z0 < 1` (e.g., the `verify_seed.py` witnesses `z0 = 309040/10^6` for 5pt
    or `308900/10^6` for 9pt on the 6757-cell M-31/M-38 emitter component).
    Then:
      1. For all `j : Nat` and all cells `i`, `scalarOrbit S.dt z0 j ≤ w (n0 + j) i ≤ 1`.
      2. For every tolerance `ε > 0`, there exists `M : Nat` such that for all `j ≥ M` and
         all cells `i`, remaining fuel satisfies `0 ≤ 1 - w (n0 + j) i < ε`. -/
theorem m41_uniform_fuel_depletion_from_threshold_witness {N : Nat} (S : SymGraphNagumo N)
    (hdt1 : S.dt ≤ 1 / 4)
    (w : Nat → Fin N → Rat)
    (hinit0 : ∀ i, (0 : Rat) ≤ w 0 i)
    (hinit1 : ∀ i, w 0 i ≤ 1)
    (hstep : ∀ n, w (n + 1) = S.step (w n))
    (n0 : Nat) (z0 : Rat)
    (hz_lo : (3 / 10 : Rat) < z0) (hz_hi : z0 < 1)
    (hwitness : ∀ i, z0 ≤ w n0 i) :
    (∀ j i, scalarOrbit S.dt z0 j ≤ w (n0 + j) i ∧ w (n0 + j) i ≤ 1) ∧
    (∀ ε : Rat, (0 : Rat) < ε →
      ∃ M : Nat, ∀ j : Nat, M ≤ j → ∀ i, (0 : Rat) ≤ 1 - w (n0 + j) i ∧ 1 - w (n0 + j) i < ε) := by
  have hbox_all : ∀ n i, (0 : Rat) ≤ w n i ∧ w n i ≤ 1 := by
    intro n
    induction n with
    | zero => intro i; exact ⟨hinit0 i, hinit1 i⟩
    | succ n ih =>
      intro i; rw [hstep n]
      exact S.step_in_box (fun j => (ih j).1) (fun j => (ih j).2) i
  have hcomp : ∀ j i, scalarOrbit S.dt z0 j ≤ w (n0 + j) i ∧ w (n0 + j) i ≤ 1 := by
    intro j
    induction j with
    | zero =>
      intro i
      simpa [scalarOrbit] using And.intro (hwitness i) (hbox_all n0 i).2
    | succ j ih =>
      intro i
      have hnext : w (n0 + (j + 1)) i = S.step (w (n0 + j)) i := by
        have : n0 + (j + 1) = (n0 + j) + 1 := by omega
        rw [this, hstep]
      rw [hnext]
      have hconst_step : scalarOrbit S.dt z0 (j + 1) = S.step (fun _ => scalarOrbit S.dt z0 j) i := by
        simp only [scalarOrbit, scalarStep]
        exact (S.step_const (scalarOrbit S.dt z0 j) i).symm
      rw [hconst_step]
      have hz_nonneg : (0 : Rat) ≤ scalarOrbit S.dt z0 j := by
        have hb := (scalarOrbit_bounds S.hdt_pos hdt1 hz_lo hz_hi j).1
        grind
      have hmono := S.step_monotone (fun _ => hz_nonneg) (fun k => (ih k).1) (fun k => (ih k).2) i
      have hhi := (S.step_in_box (fun k => (hbox_all (n0 + j) k).1) (fun k => (hbox_all (n0 + j) k).2) i).2
      exact ⟨hmono, hhi⟩
  refine ⟨hcomp, ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := scalarOrbit_approaches_one S.hdt_pos hdt1 hz_lo hz_hi hε
  refine ⟨M, fun j hj i => ?_⟩
  have h1 := (hM j hj).1
  have h2 := hcomp j i
  exact ⟨by grind, by grind⟩

end M41ScalarReset
