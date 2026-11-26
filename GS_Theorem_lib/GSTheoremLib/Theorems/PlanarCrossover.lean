/-
  Lean 4 Formalization of the Confirmed Theorem:
    "Fixed-Port Monotone Dual-Rail Inversion Obstruction &
     Strictly Planar Zero-Crossover Logic Gadgets"
  Source verdict:
    coordination/confirm/2026-11-21_planar_nonmonotone_crossover/VERDICT.md
  Zero external dependencies (pure Lean 4 core `Init`, zero `sorry`).
-/

namespace PlanarNonmonotoneCrossover

/-! ## Part 1: Monotone Circuits & Fixed-Port Dual-Rail Obstruction (Proposition 1) -/

/-- Pointwise order on booleans: `false ≤ false`, `false ≤ true`, `true ≤ true`. -/
def boolLe (a b : Bool) : Prop :=
  a = true → b = true

theorem boolLe_refl (a : Bool) : boolLe a a := fun h => h

/-- Pointwise order on equal-length boolean lists. -/
def listBoolLe : List Bool → List Bool → Prop
  | [], [] => True
  | a :: as, b :: bs => boolLe a b ∧ listBoolLe as bs
  | _, _ => False

theorem listBoolLe_map {α : Type} (f g : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, boolLe (f x) (g x)) → listBoolLe (xs.map f) (xs.map g)
  | [], _ => trivial
  | x :: xs, h =>
    ⟨h x (List.mem_cons_self),
     listBoolLe_map f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

/-- A boolean gate of arbitrary arity is monotone if it preserves `listBoolLe`. -/
def IsMonotone (f : List Bool → Bool) : Prop :=
  ∀ xs ys, listBoolLe xs ys → boolLe (f xs) (f ys)

/-- A node in a topologically ordered monotone DAG circuit (`u` only depends on `p < u`). -/
inductive MonoNode (u : Nat) where
  | input (idx : Nat)
  | gate (preds : List Nat) (f : List Bool → Bool) (hmono : IsMonotone f)
         (hdag : ∀ p ∈ preds, p < u)

/-- A finite monotone DAG circuit over nodes `0, 1, ..., n - 1`. -/
structure MonoCircuit where
  size : Nat
  node : (u : Nat) → MonoNode u

/-- Fuel-indexed structural evaluation of a monotone DAG circuit. -/
def MonoCircuit.evalAux (C : MonoCircuit) (env : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, u =>
    match C.node u with
    | .input idx => env idx
    | .gate preds f _ _ => f (preds.map (C.evalAux env fuel))

/-- Canonical evaluation of a topologically ordered monotone DAG circuit at node `u`. -/
def MonoCircuit.eval (C : MonoCircuit) (env : Nat → Bool) (u : Nat) : Bool :=
  C.evalAux env (u + 1) u

private theorem list_map_ext {α β : Type} {f g : α → β} :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.map f = xs.map g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map]
    rw [h x List.mem_cons_self, list_map_ext xs (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem MonoCircuit.evalAux_eq_of_gt (C : MonoCircuit) (env : Nat → Bool) :
    ∀ (k₁ k₂ u : Nat), u < k₁ → u < k₂ → C.evalAux env k₁ u = C.evalAux env k₂ u
  | 0, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _, 0, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | k₁ + 1, k₂ + 1, u, h1, h2 => by
    simp only [MonoCircuit.evalAux]
    cases h : C.node u with
    | input idx => rfl
    | gate preds f _ hdag =>
      apply congrArg f
      apply list_map_ext
      intro p hp
      have hpu : p < u := hdag p hp
      exact evalAux_eq_of_gt C env k₁ k₂ p (Nat.lt_of_lt_of_le hpu (Nat.lt_succ_iff.mp h1))
        (Nat.lt_of_lt_of_le hpu (Nat.lt_succ_iff.mp h2))

theorem MonoCircuit.eval_input (C : MonoCircuit) (env : Nat → Bool) {u idx : Nat}
    (h : C.node u = .input idx) : C.eval env u = env idx := by
  simp only [MonoCircuit.eval, MonoCircuit.evalAux, h]

theorem MonoCircuit.eval_gate (C : MonoCircuit) (env : Nat → Bool) {u : Nat}
    {preds : List Nat} {f : List Bool → Bool} {hmono : IsMonotone f}
    {hdag : ∀ p ∈ preds, p < u} (h : C.node u = .gate preds f hmono hdag) :
    C.eval env u = f (preds.map (C.eval env)) := by
  simp only [MonoCircuit.eval, MonoCircuit.evalAux, h]
  apply congrArg f
  apply list_map_ext
  intro p hp
  exact MonoCircuit.evalAux_eq_of_gt C env u (p + 1) p (hdag p hp) (Nat.lt_succ_self p)

/-- Proposition 1A (Single-rail monotonicity): every monotone DAG computes a monotone function. -/
theorem MonoCircuit.eval_monotone (C : MonoCircuit) {env₁ env₂ : Nat → Bool}
    (henv : ∀ i, boolLe (env₁ i) (env₂ i)) :
    ∀ u, boolLe (C.eval env₁ u) (C.eval env₂ u) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    cases h : C.node u with
    | input idx =>
      rw [C.eval_input env₁ h, C.eval_input env₂ h]
      exact henv idx
    | gate preds f hmono hdag =>
      rw [C.eval_gate env₁ h, C.eval_gate env₂ h]
      apply hmono
      apply listBoolLe_map
      intro p hp
      exact ih p (hdag p hp)

/-- Corollary 1A: No monotone DAG circuit can compute single-rail `NOT`. -/
theorem monotone_circuit_no_single_rail_not (C : MonoCircuit) (out : Nat) :
    ¬ (∀ b : Bool, C.eval (fun _ => b) out = !b) := by
  intro hnot
  have hle : boolLe (C.eval (fun _ => false) out) (C.eval (fun _ => true) out) :=
    C.eval_monotone (fun _ _ => rfl) out
  have h0 : C.eval (fun _ => false) out = true := hnot false
  have h1 : C.eval (fun _ => true) out = false := hnot true
  have hcontra : false = true := by
    rw [← h1]
    exact hle h0
  cases hcontra

/-- Directed edge relation in `C`: `p` feeds into `u`. -/
def MonoCircuit.HasEdge (C : MonoCircuit) (p u : Nat) : Prop :=
  ∃ preds f hmono hdag, C.node u = .gate preds f hmono hdag ∧ p ∈ preds

/-- A directed path in `C` from `src` to `dst`, represented as the list of all vertices on it. -/
inductive MonoCircuit.DPath (C : MonoCircuit) : Nat → Nat → List Nat → Prop where
  | single (u : Nat) : C.DPath u u [u]
  | snoc {src p u : Nat} {vs : List Nat} :
      C.DPath src p vs → C.HasEdge p u → C.DPath src u (vs ++ [u])

/-- Classification of vertices under two complementary dual-rail inputs `env10` and `env01`. -/
def IsTypeA (C : MonoCircuit) (env10 env01 : Nat → Bool) (u : Nat) : Prop :=
  C.eval env10 u = true ∧ C.eval env01 u = false

def IsTypeB (C : MonoCircuit) (env10 env01 : Nat → Bool) (u : Nat) : Prop :=
  C.eval env10 u = false ∧ C.eval env01 u = true

theorem typeA_typeB_disjoint (C : MonoCircuit) (env10 env01 : Nat → Bool) (u : Nat) :
    ¬ (IsTypeA C env10 env01 u ∧ IsTypeB C env10 env01 u) := by
  rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
  rw [h1] at h2
  cases h2

/-- Helper: if no predecessor of a gate is Type A, then pointwise `eval env10 ≤ eval env01`. -/
private theorem no_typeA_pred_implies_le (C : MonoCircuit) (env10 env01 : Nat → Bool)
    (preds : List Nat) (hno : ∀ p ∈ preds, ¬ IsTypeA C env10 env01 p) :
    listBoolLe (preds.map (C.eval env10)) (preds.map (C.eval env01)) := by
  apply listBoolLe_map
  intro p hp h10
  cases h01 : C.eval env01 p with
  | true => rfl
  | false => exact False.elim (hno p hp ⟨h10, h01⟩)

/-- Helper: if no predecessor of a gate is Type B, then pointwise `eval env01 ≤ eval env10`. -/
private theorem no_typeB_pred_implies_le (C : MonoCircuit) (env10 env01 : Nat → Bool)
    (preds : List Nat) (hno : ∀ p ∈ preds, ¬ IsTypeB C env10 env01 p) :
    listBoolLe (preds.map (C.eval env01)) (preds.map (C.eval env10)) := by
  apply listBoolLe_map
  intro p hp h01
  cases h10 : C.eval env10 p with
  | true => rfl
  | false => exact False.elim (hno p hp ⟨h10, h01⟩)

/-- Helper: decidable search in a finite list for a Type A element. -/
private theorem exists_typeA_or_forall_not (C : MonoCircuit) (env10 env01 : Nat → Bool) :
    ∀ (ps : List Nat), (∃ p ∈ ps, IsTypeA C env10 env01 p) ∨ (∀ p ∈ ps, ¬ IsTypeA C env10 env01 p)
  | [] => Or.inr (fun _ h => nomatch h)
  | p :: ps =>
    match h10 : C.eval env10 p, h01 : C.eval env01 p with
    | true, false => Or.inl ⟨p, List.mem_cons_self, ⟨h10, h01⟩⟩
    | false, _ =>
      match exists_typeA_or_forall_not C env10 env01 ps with
      | Or.inl ⟨q, hq, hA⟩ => Or.inl ⟨q, List.mem_cons_of_mem p hq, hA⟩
      | Or.inr hno =>
        Or.inr (fun q hq => by
          cases hq with
          | head => rintro ⟨ht, _⟩; rw [h10] at ht; cases ht
          | tail _ hmem => exact hno q hmem)
    | true, true =>
      match exists_typeA_or_forall_not C env10 env01 ps with
      | Or.inl ⟨q, hq, hA⟩ => Or.inl ⟨q, List.mem_cons_of_mem p hq, hA⟩
      | Or.inr hno =>
        Or.inr (fun q hq => by
          cases hq with
          | head => rintro ⟨_, hf⟩; rw [h01] at hf; cases hf
          | tail _ hmem => exact hno q hmem)

private theorem exists_typeB_or_forall_not (C : MonoCircuit) (env10 env01 : Nat → Bool) :
    ∀ (ps : List Nat), (∃ p ∈ ps, IsTypeB C env10 env01 p) ∨ (∀ p ∈ ps, ¬ IsTypeB C env10 env01 p)
  | [] => Or.inr (fun _ h => nomatch h)
  | p :: ps =>
    match h10 : C.eval env10 p, h01 : C.eval env01 p with
    | false, true => Or.inl ⟨p, List.mem_cons_self, ⟨h10, h01⟩⟩
    | true, _ =>
      match exists_typeB_or_forall_not C env10 env01 ps with
      | Or.inl ⟨q, hq, hB⟩ => Or.inl ⟨q, List.mem_cons_of_mem p hq, hB⟩
      | Or.inr hno =>
        Or.inr (fun q hq => by
          cases hq with
          | head => rintro ⟨hf, _⟩; rw [h10] at hf; cases hf
          | tail _ hmem => exact hno q hmem)
    | false, false =>
      match exists_typeB_or_forall_not C env10 env01 ps with
      | Or.inl ⟨q, hq, hB⟩ => Or.inl ⟨q, List.mem_cons_of_mem p hq, hB⟩
      | Or.inr hno =>
        Or.inr (fun q hq => by
          cases hq with
          | head => rintro ⟨_, ht⟩; rw [h01] at ht; cases ht
          | tail _ hmem => exact hno q hmem)

/-- Key Backtracking Lemma (Type A): every Type A vertex has an all-Type-A directed path
    from a Type A input vertex. -/
theorem backtrack_typeA (C : MonoCircuit) (env10 env01 : Nat → Bool) :
    ∀ u, IsTypeA C env10 env01 u →
      ∃ src idx vs,
        C.node src = .input idx ∧
        C.DPath src u vs ∧
        (∀ v ∈ vs, IsTypeA C env10 env01 v) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hAu
    cases h : C.node u with
    | input idx =>
      exact ⟨u, idx, [u], h, .single u, fun v hv => by
        cases hv with
        | head => exact hAu
        | tail _ hm => cases hm⟩
    | gate preds f hmono hdag =>
      cases exists_typeA_or_forall_not C env10 env01 preds with
      | inl hex =>
        obtain ⟨p, hp, hAp⟩ := hex
        obtain ⟨src, idx, vs, hsrc, hpath, hall⟩ := ih p (hdag p hp) hAp
        refine ⟨src, idx, vs ++ [u], hsrc,
          .snoc hpath ⟨preds, f, hmono, hdag, h, hp⟩, ?_⟩
        intro v hv
        rw [List.mem_append] at hv
        cases hv with
        | inl h1 => exact hall v h1
        | inr h2 =>
          cases h2 with
          | head => exact hAu
          | tail _ hm => cases hm
      | inr hno =>
        have hle := no_typeA_pred_implies_le C env10 env01 preds hno
        have h10 : f (preds.map (C.eval env10)) = true := by
          rw [← C.eval_gate env10 h]; exact hAu.1
        have h01 : f (preds.map (C.eval env01)) = false := by
          rw [← C.eval_gate env01 h]; exact hAu.2
        have hcontra : false = true := by
          rw [← h01]; exact hmono _ _ hle h10
        cases hcontra

/-- Key Backtracking Lemma (Type B): every Type B vertex has an all-Type-B directed path
    from a Type B input vertex. -/
theorem backtrack_typeB (C : MonoCircuit) (env10 env01 : Nat → Bool) :
    ∀ u, IsTypeB C env10 env01 u →
      ∃ src idx vs,
        C.node src = .input idx ∧
        C.DPath src u vs ∧
        (∀ v ∈ vs, IsTypeB C env10 env01 v) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hBu
    cases h : C.node u with
    | input idx =>
      exact ⟨u, idx, [u], h, .single u, fun v hv => by
        cases hv with
        | head => exact hBu
        | tail _ hm => cases hm⟩
    | gate preds f hmono hdag =>
      cases exists_typeB_or_forall_not C env10 env01 preds with
      | inl hex =>
        obtain ⟨p, hp, hBp⟩ := hex
        obtain ⟨src, idx, vs, hsrc, hpath, hall⟩ := ih p (hdag p hp) hBp
        refine ⟨src, idx, vs ++ [u], hsrc,
          .snoc hpath ⟨preds, f, hmono, hdag, h, hp⟩, ?_⟩
        intro v hv
        rw [List.mem_append] at hv
        cases hv with
        | inl h1 => exact hall v h1
        | inr h2 =>
          cases h2 with
          | head => exact hBu
          | tail _ hm => cases hm
      | inr hno =>
        have hle := no_typeB_pred_implies_le C env10 env01 preds hno
        have h01 : f (preds.map (C.eval env01)) = true := by
          rw [← C.eval_gate env01 h]; exact hBu.2
        have h10 : f (preds.map (C.eval env10)) = false := by
          rw [← C.eval_gate env10 h]; exact hBu.1
        have hcontra : false = true := by
          rw [← h10]; exact hmono _ _ hle h01
        cases hcontra

/-- Proposition 1B (Combinatorial Core of the Fixed-Port Dual-Rail Obstruction):
    Suppose a monotone DAG circuit has two designated input ports `inL` (input index 0)
    and `inR` (input index 1), with all other input indices constant across the two valid
    dual-rail encodings `env10 = (true, false)` and `env01 = (false, true)`.
    If outputs `(outL, outR)` implement dual-rail inversion `(x1, x0)`, then there exist
    two strictly vertex-disjoint directed paths:
      - `vsA` from `inL` to `outR` (crossing top-left to bottom-right),
      - `vsB` from `inR` to `outL` (crossing top-right to bottom-left). -/
theorem dual_rail_not_forces_disjoint_crossing_paths
    (C : MonoCircuit) (inL inR outL outR : Nat)
    (env10 env01 : Nat → Bool)
    (h_inL_unique : ∀ u idx, C.node u = .input idx → env10 idx = true → env01 idx = false → u = inL)
    (h_inR_unique : ∀ u idx, C.node u = .input idx → env10 idx = false → env01 idx = true → u = inR)
    (h_outL : IsTypeB C env10 env01 outL)
    (h_outR : IsTypeA C env10 env01 outR) :
    ∃ vsA vsB,
      C.DPath inL outR vsA ∧
      C.DPath inR outL vsB ∧
      (∀ v ∈ vsA, v ∉ vsB) := by
  obtain ⟨srcA, idxA, vsA, hnodeA, hpathA, hallA⟩ := backtrack_typeA C env10 env01 outR h_outR
  obtain ⟨srcB, idxB, vsB, hnodeB, hpathB, hallB⟩ := backtrack_typeB C env10 env01 outL h_outL
  have hsrcA_mem : srcA ∈ vsA := by
    cases hpathA with
    | single => exact List.mem_cons_self
    | snoc h1 _ =>
      -- prove head of any DPath is in vs
      have mem_start : ∀ {a b vs}, C.DPath a b vs → a ∈ vs := by
        intro a b vs hp
        induction hp with
        | single => exact List.mem_cons_self
        | snoc _ _ ih => exact List.mem_append_left _ ih
      exact List.mem_append_left _ (mem_start h1)
  have hsrcB_mem : srcB ∈ vsB := by
    have mem_start : ∀ {a b vs}, C.DPath a b vs → a ∈ vs := by
      intro a b vs hp
      induction hp with
      | single => exact List.mem_cons_self
      | snoc _ _ ih => exact List.mem_append_left _ ih
    exact mem_start hpathB
  have hA_src : C.eval env10 srcA = true ∧ C.eval env01 srcA = false := hallA srcA hsrcA_mem
  have hB_src : C.eval env10 srcB = false ∧ C.eval env01 srcB = true := hallB srcB hsrcB_mem
  rw [C.eval_input env10 hnodeA, C.eval_input env01 hnodeA] at hA_src
  rw [C.eval_input env10 hnodeB, C.eval_input env01 hnodeB] at hB_src
  have heqA : srcA = inL := h_inL_unique srcA idxA hnodeA hA_src.1 hA_src.2
  have heqB : srcB = inR := h_inR_unique srcB idxB hnodeB hB_src.1 hB_src.2
  subst heqA
  subst heqB
  refine ⟨vsA, vsB, hpathA, hpathB, ?_⟩
  intro v hvA hvB
  exact typeA_typeB_disjoint C env10 env01 v ⟨hallA v hvA, hallB v hvB⟩

/-- Explicit topological boundary hypothesis (Jordan curve theorem on a closed rectangle):
    in any planar disk embedding with alternating boundary ports `(inL, inR)` on top and
    `(outL, outR)` on bottom, no two vertex-disjoint paths can connect `inL → outR` and `inR → outL`. -/
def PlanarDiskCrossingObstruction (C : MonoCircuit) (inL inR outL outR : Nat) : Prop :=
  ∀ vsA vsB, C.DPath inL outR vsA → C.DPath inR outL vsB → (∀ v ∈ vsA, v ∉ vsB) → False

/-- Proposition 1B Corollary: Under the planar disk boundary obstruction, no monotone DAG
    can implement fixed-port dual-rail inversion. -/
theorem dual_rail_not_impossible_in_planar_disk
    (C : MonoCircuit) (inL inR outL outR : Nat)
    (env10 env01 : Nat → Bool)
    (h_planar : PlanarDiskCrossingObstruction C inL inR outL outR)
    (h_inL_unique : ∀ u idx, C.node u = .input idx → env10 idx = true → env01 idx = false → u = inL)
    (h_inR_unique : ∀ u idx, C.node u = .input idx → env10 idx = false → env01 idx = true → u = inR)
    (h_outL : IsTypeB C env10 env01 outL)
    (h_outR : IsTypeA C env10 env01 outR) :
    False := by
  obtain ⟨vsA, vsB, hA, hB, hdisj⟩ :=
    dual_rail_not_forces_disjoint_crossing_paths C inL inR outL outR env10 env01
      h_inL_unique h_inR_unique h_outL h_outR
  exact h_planar vsA vsB hA hB hdisj

/-- Standard single-port input representation: each external input index `idx` is represented
    by at most one `.input` node in the circuit (fanout is performed by internal gates). -/
def InputPortUnique (C : MonoCircuit) : Prop :=
  ∀ u₁ u₂ idx, C.node u₁ = .input idx → C.node u₂ = .input idx → u₁ = u₂

/-- Corollary 1B (Single-Port Input Model):
    If `C` has unique input nodes per input index (`InputPortUnique C`), with designated input
    ports `inL` (index `idxL`) and `inR` (index `idxR`), and all other input indices are constant
    across `env10` and `env01` (e.g. `CONST_0`/`CONST_1` sources), then `h_inL_unique` and
    `h_inR_unique` follow automatically, yielding the planar disk obstruction. -/
theorem dual_rail_not_impossible_single_port_planar_disk
    (C : MonoCircuit) (inL inR idxL idxR outL outR : Nat)
    (env10 env01 : Nat → Bool)
    (h_port_uniq : InputPortUnique C)
    (h_node_inL : C.node inL = .input idxL)
    (h_node_inR : C.node inR = .input idxR)
    (h_env_other : ∀ idx, idx ≠ idxL → idx ≠ idxR → env10 idx = env01 idx)
    (h_env_L : env10 idxL = true ∧ env01 idxL = false)
    (h_env_R : env10 idxR = false ∧ env01 idxR = true)
    (h_planar : PlanarDiskCrossingObstruction C inL inR outL outR)
    (h_outL : IsTypeB C env10 env01 outL)
    (h_outR : IsTypeA C env10 env01 outR) :
    False := by
  apply dual_rail_not_impossible_in_planar_disk C inL inR outL outR env10 env01 h_planar
  · intro u idx hnode h10 h01
    by_cases hL : idx = idxL
    · subst hL; exact h_port_uniq u inL idx hnode h_node_inL
    · by_cases hR : idx = idxR
      · subst hR; rw [h_env_R.1] at h10; cases h10
      · have heq := h_env_other idx hL hR
        rw [h10, h01] at heq; cases heq
  · intro u idx hnode h10 h01
    by_cases hR : idx = idxR
    · subst hR; exact h_port_uniq u inR idx hnode h_node_inR
    · by_cases hL : idx = idxL
      · subst hL; rw [h_env_L.1] at h10; cases h10
      · have heq := h_env_other idx hL hR
        rw [h10, h01] at heq; cases heq
  · exact h_outL
  · exact h_outR


/-! ## Part 2: Exact Integer Geometry & Verification of the 3 Confirmed Planar Gadgets (Proposition 2) -/

inductive GateKind where
  | IN (idx : Nat)
  | CONST_1
  | FANOUT
  | NAND
  | INH
  | OUT
  deriving DecidableEq, Repr

structure GNode where
  id : Nat
  kind : GateKind
  x : Int
  y : Int
  inputs : List Nat
  deriving DecidableEq, Repr

structure Gadget where
  nodes : List GNode
  inputIds : List Nat
  outputIds : List Nat
  deriving Repr

def Gadget.getNode (G : Gadget) (id : Nat) : Option GNode :=
  G.nodes.find? (fun n => n.id == id)

def Gadget.edges (G : Gadget) : List (Nat × Nat) :=
  G.nodes.foldr (fun n acc => (n.inputs.map (fun src => (src, n.id))) ++ acc) []

/-- 2D exact integer cross product `(a - o) × (b - o)`. -/
def cross2 (o a b : GNode) : Int :=
  (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x)

def onSegment (p q r : GNode) : Bool :=
  min p.x r.x ≤ q.x && q.x ≤ max p.x r.x &&
  min p.y r.y ≤ q.y && q.y ≤ max p.y r.y

/-- Exact integer closed-segment intersection test for two edges without shared endpoints. -/
def segmentsIntersect (p1 q1 p2 q2 : GNode) : Bool :=
  if max p1.x q1.x < min p2.x q2.x || max p2.x q2.x < min p1.x q1.x then false
  else if max p1.y q1.y < min p2.y q2.y || max p2.y q2.y < min p1.y q1.y then false
  else
    let d1 := cross2 p2 q2 p1
    let d2 := cross2 p2 q2 q1
    let d3 := cross2 p1 q1 p2
    let d4 := cross2 p1 q1 q2
    if ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
       ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)) then true
    else if d1 == 0 && onSegment p2 p1 q2 then true
    else if d2 == 0 && onSegment p2 q1 q2 then true
    else if d3 == 0 && onSegment p1 p2 q1 then true
    else if d4 == 0 && onSegment p1 q2 q1 then true
    else false

/-- Check that two edges `(u1, v1)` and `(u2, v2)` do not improperly cross or overlap. -/
def edgePairValid (G : Gadget) (e1 e2 : Nat × Nat) : Bool :=
  let (u1, v1) := e1
  let (u2, v2) := e2
  match G.getNode u1, G.getNode v1, G.getNode u2, G.getNode v2 with
  | some p1, some q1, some p2, some q2 =>
    -- Check shared endpoints
    let shareCount :=
      (if u1 == u2 || u1 == v2 then 1 else 0) +
      (if v1 == u2 || v1 == v2 then 1 else 0)
    if shareCount == 0 then
      !segmentsIntersect p1 q1 p2 q2
    else if shareCount == 1 then
      let (c, a, b) :=
        if u1 == u2 then (p1, q1, q2)
        else if u1 == v2 then (p1, q1, p2)
        else if v1 == u2 then (q1, p1, q2)
        else (q1, p1, p2)
      if cross2 c a b == 0 then
        -- Collinear from shared endpoint `c`: must point in strictly opposite directions
        (a.x - c.x) * (b.x - c.x) + (a.y - c.y) * (b.y - c.y) < 0
      else
        true
    else
      false -- parallel duplicate edge forbidden
  | _, _, _, _ => false

def allPairsValid (G : Gadget) : List (Nat × Nat) → Bool
  | [] => true
  | e :: es => es.all (fun e2 => edgePairValid G e e2) && allPairsValid G es

def allDistinctCoords : List GNode → Bool
  | [] => true
  | n :: ns => ns.all (fun m => !(n.x == m.x && n.y == m.y)) && allDistinctCoords ns

def allDistinctIds : List GNode → Bool
  | [] => true
  | n :: ns => ns.all (fun m => n.id != m.id) && allDistinctIds ns

def strictlyOrderedX (G : Gadget) : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    match G.getNode a, G.getNode b with
    | some na, some nb => na.x < nb.x && strictlyOrderedX G (b :: rest)
    | _, _ => false

/-- Verify all structural, degree, port-ordering, strict y-monotonicity, local INH slope-order,
    and pairwise non-crossing invariants of a planar gadget. -/
def Gadget.verifyPlanar (G : Gadget) : Bool :=
  let es := G.edges
  let outDeg (id : Nat) : Nat := (es.filter (fun e => e.1 == id)).length
  let degOk := G.nodes.all fun n =>
    let indeg := n.inputs.length
    let odeg := outDeg n.id
    match n.kind with
    | .IN _ | .CONST_1 => indeg == 0 && odeg == 1
    | .FANOUT => indeg == 1 && odeg == 2
    | .NAND => indeg == 2 && odeg == 1
    | .INH =>
      indeg == 2 && odeg == 1 &&
      match n.inputs with
      | [pId, qId] =>
        match G.getNode pId, G.getNode qId with
        | some p, some q =>
          -- Both predecessor x-order (p.x < q.x) AND local incoming slope order at node `n`:
          -- (p.x - n.x)/(p.y - n.y) < (q.x - n.x)/(q.y - n.y) since p.y > n.y and q.y > n.y
          p.x < q.x && (p.x - n.x) * (q.y - n.y) < (q.x - n.x) * (p.y - n.y)
        | _, _ => false
      | _ => false
    | .OUT => indeg == 1 && odeg == 0
  let yMonoOk := es.all fun (src, dst) =>
    match G.getNode src, G.getNode dst with
    | some ns, some nd => ns.y > nd.y
    | _, _ => false
  allDistinctIds G.nodes &&
  allDistinctCoords G.nodes &&
  degOk &&
  strictlyOrderedX G G.inputIds &&
  strictlyOrderedX G G.outputIds &&
  yMonoOk &&
  allPairsValid G es

/-- Fuel-bounded exact boolean evaluation of a gadget (nodes are stored in topological order,
    so fuel = `G.nodes.length + 1` always suffices). -/
def Gadget.evalNode (G : Gadget) (env : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, id =>
    match G.getNode id with
    | none => false
    | some n =>
      match n.kind with
      | .IN idx => env idx
      | .CONST_1 => true
      | .FANOUT | .OUT =>
        match n.inputs with
        | [src] => G.evalNode env fuel src
        | _ => false
      | .NAND =>
        match n.inputs with
        | [a, b] => !(G.evalNode env fuel a && G.evalNode env fuel b)
        | _ => false
      | .INH =>
        match n.inputs with
        | [p, q] => G.evalNode env fuel p && !(G.evalNode env fuel q)
        | _ => false

def Gadget.evalOut (G : Gadget) (a b : Bool) (outId : Nat) : Bool :=
  G.evalNode (fun i => if i == 0 then a else b) (G.nodes.length + 1) outId


/-! ### Explicit Confirmed Gadgets (Exact Coordinates from `verify_planar_gadgets.py`) -/

/-- Gadget 1: 4-NAND strictly planar XOR(a, b). -/
def xorGadget : Gadget :=
  { nodes := [
      { id := 0, kind := .IN 0,   x := -4, y := 10, inputs := [] },
      { id := 1, kind := .IN 1,   x :=  4, y := 10, inputs := [] },
      { id := 2, kind := .FANOUT, x := -2, y :=  9, inputs := [0] },
      { id := 3, kind := .FANOUT, x :=  2, y :=  9, inputs := [1] },
      { id := 4, kind := .NAND,   x :=  0, y :=  7, inputs := [2, 3] },
      { id := 5, kind := .FANOUT, x :=  0, y :=  6, inputs := [4] },
      { id := 6, kind := .NAND,   x := -1, y :=  4, inputs := [2, 5] },
      { id := 7, kind := .NAND,   x :=  1, y :=  4, inputs := [5, 3] },
      { id := 8, kind := .NAND,   x :=  0, y :=  2, inputs := [6, 7] },
      { id := 9, kind := .OUT,    x :=  0, y :=  0, inputs := [8] }
    ]
    inputIds := [0, 1]
    outputIds := [9] }

/-- Gadget 2: 12-NAND (3-XOR) strictly planar zero-crossover SWAP(a, b) = (b, a). -/
def swapGadget : Gadget :=
  { nodes := [
      { id :=  0, kind := .IN 0,   x := -10, y := 22, inputs := [] },
      { id :=  1, kind := .IN 1,   x :=  10, y := 22, inputs := [] },
      { id :=  2, kind := .FANOUT, x := -10, y := 21, inputs := [0] },
      { id :=  3, kind := .FANOUT, x :=  10, y := 21, inputs := [1] },
      -- mid XOR (cx = 0, top_y = 19)
      { id :=  4, kind := .FANOUT, x :=  -2, y := 19, inputs := [2] },
      { id :=  5, kind := .FANOUT, x :=   2, y := 19, inputs := [3] },
      { id :=  6, kind := .NAND,   x :=   0, y := 17, inputs := [4, 5] },
      { id :=  7, kind := .FANOUT, x :=   0, y := 16, inputs := [6] },
      { id :=  8, kind := .NAND,   x :=  -1, y := 14, inputs := [4, 7] },
      { id :=  9, kind := .NAND,   x :=   1, y := 14, inputs := [7, 5] },
      { id := 10, kind := .NAND,   x :=   0, y := 12, inputs := [8, 9] },
      { id := 11, kind := .FANOUT, x :=   0, y := 11, inputs := [10] },
      -- left XOR (cx = -6, top_y = 9)
      { id := 12, kind := .FANOUT, x :=  -8, y :=  9, inputs := [2] },
      { id := 13, kind := .FANOUT, x :=  -4, y :=  9, inputs := [11] },
      { id := 14, kind := .NAND,   x :=  -6, y :=  7, inputs := [12, 13] },
      { id := 15, kind := .FANOUT, x :=  -6, y :=  6, inputs := [14] },
      { id := 16, kind := .NAND,   x :=  -7, y :=  4, inputs := [12, 15] },
      { id := 17, kind := .NAND,   x :=  -5, y :=  4, inputs := [15, 13] },
      { id := 18, kind := .NAND,   x :=  -6, y :=  2, inputs := [16, 17] },
      -- right XOR (cx = 6, top_y = 9)
      { id := 19, kind := .FANOUT, x :=   4, y :=  9, inputs := [11] },
      { id := 20, kind := .FANOUT, x :=   8, y :=  9, inputs := [3] },
      { id := 21, kind := .NAND,   x :=   6, y :=  7, inputs := [19, 20] },
      { id := 22, kind := .FANOUT, x :=   6, y :=  6, inputs := [21] },
      { id := 23, kind := .NAND,   x :=   5, y :=  4, inputs := [19, 22] },
      { id := 24, kind := .NAND,   x :=   7, y :=  4, inputs := [22, 20] },
      { id := 25, kind := .NAND,   x :=   6, y :=  2, inputs := [23, 24] },
      -- outputs
      { id := 26, kind := .OUT,    x :=  -6, y :=  0, inputs := [18] },
      { id := 27, kind := .OUT,    x :=   6, y :=  0, inputs := [25] }
    ]
    inputIds := [0, 1]
    outputIds := [26, 27] }

/-- Gadget 3: 3-INHIBIT (+ 2 CONST_1) strictly planar NAND(a, b). -/
def inhibitToNandGadget : Gadget :=
  { nodes := [
      { id := 0, kind := .CONST_1, x := -6, y := 10, inputs := [] },
      { id := 1, kind := .IN 0,    x := -2, y := 10, inputs := [] },
      { id := 2, kind := .CONST_1, x :=  1, y :=  9, inputs := [] },
      { id := 3, kind := .IN 1,    x :=  4, y := 10, inputs := [] },
      { id := 4, kind := .INH,     x :=  2, y :=  7, inputs := [2, 3] },
      { id := 5, kind := .INH,     x := -1, y :=  4, inputs := [1, 4] },
      { id := 6, kind := .INH,     x := -3, y :=  2, inputs := [0, 5] },
      { id := 7, kind := .OUT,     x := -3, y :=  0, inputs := [6] }
    ]
    inputIds := [1, 3]
    outputIds := [7] }


/-! ### Kernel-Verified Theorems (Proposition 2: Planarity, Counts, and Exhaustive Truth Tables) -/

theorem xorGadget_is_strictly_planar : xorGadget.verifyPlanar = true := by decide

theorem xorGadget_truth_table : ∀ a b : Bool, xorGadget.evalOut a b 9 = xor a b := by decide

theorem xorGadget_counts :
    (xorGadget.nodes.filter (fun n => n.kind == .NAND)).length = 4 ∧
    (xorGadget.nodes.filter (fun n => n.kind == .FANOUT)).length = 3 := by decide

theorem swapGadget_is_strictly_planar : swapGadget.verifyPlanar = true := by decide

theorem swapGadget_truth_table :
    ∀ a b : Bool, (swapGadget.evalOut a b 26, swapGadget.evalOut a b 27) = (b, a) := by decide

theorem swapGadget_counts :
    (swapGadget.nodes.filter (fun n => n.kind == .NAND)).length = 12 ∧
    (swapGadget.nodes.filter (fun n => n.kind == .FANOUT)).length = 12 := by decide

theorem inhibitToNandGadget_is_strictly_planar :
    inhibitToNandGadget.verifyPlanar = true := by decide

theorem inhibitToNandGadget_truth_table :
    ∀ a b : Bool, inhibitToNandGadget.evalOut a b 7 = !(a && b) := by decide

theorem inhibitToNandGadget_counts :
    (inhibitToNandGadget.nodes.filter (fun n => n.kind == .INH)).length = 3 ∧
    (inhibitToNandGadget.nodes.filter (fun n => n.kind == .CONST_1)).length = 2 := by decide

end PlanarNonmonotoneCrossover
