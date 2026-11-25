import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Counterexample to jinni's Cheeger--Pareto conjecture B

Sources:
* https://mathoverflow.net/questions/506070
* https://math.stackexchange.com/questions/5118288

An edge set contains each undirected edge once, in increasing vertex order.
The Cheeger constant uses the *number of vertices*, not the graph volume.
The universal statement below is the pointwise form of the proposed bound
on the minimum over Pareto-efficient feasible vectors. Vectors are real-valued.
-/

open scoped BigOperators

namespace CheegerPareto

abbrev EdgeSet (n : ℕ) := Finset (Fin n × Fin n)

def OrderedEdges {n : ℕ} (E : EdgeSet n) : Prop :=
  ∀ e ∈ E, e.1 < e.2

def cutSize {n : ℕ} (E : EdgeSet n) (S : Finset (Fin n)) : ℕ :=
  (E.filter fun e => (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)).card

def Feasible {n : ℕ} (E : EdgeSet n) (z : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ z v) ∧
  ∀ S : Finset (Fin n), S.card ≤ n / 2 →
    (∑ v ∈ S, z v) ≤ (cutSize E S : ℝ)

def Pareto {n : ℕ} (E : EdgeSet n) (z : Fin n → ℝ) : Prop :=
  Feasible E z ∧ ∀ y : Fin n → ℝ,
    Feasible E y → (∀ v, z v ≤ y v) → y = z

/-- The lower bound on all admissible nonempty cuts, with attainment.
Because the denominators are positive, this is exactly the minimum ratio. -/
def IsCheeger {n : ℕ} (E : EdgeSet n) (h : ℝ) : Prop :=
  (∀ S : Finset (Fin n), 0 < S.card → S.card ≤ n / 2 →
    h * (S.card : ℝ) ≤ (cutSize E S : ℝ)) ∧
  ∃ S : Finset (Fin n), 0 < S.card ∧ S.card ≤ n / 2 ∧
    h * (S.card : ℝ) = (cutSize E S : ℝ)

/-- Equivalent pointwise form of Conjecture B. -/
def ConjectureB : Prop :=
  ∀ (n : ℕ) (E : EdgeSet n), 2 ≤ n → OrderedEdges E →
    ∀ (h : ℝ), IsCheeger E h → ∀ z : Fin n → ℝ, Pareto E z →
      ((n / 2 : ℕ) : ℝ) * h ≤ ∑ v, z v

/-- The attained-minimum and pointwise formulations of a lower bound agree. -/
theorem least_mass_iff {n : ℕ} (E : EdgeSet n) (r L : ℝ)
    (hr : IsLeast {t : ℝ | ∃ z, Pareto E z ∧ (∑ v, z v) = t} r) :
    L ≤ r ↔ ∀ z, Pareto E z → L ≤ ∑ v, z v := by
  constructor
  · intro h z hz
    exact le_trans h (hr.2 ⟨z, hz, rfl⟩)
  · intro h
    obtain ⟨z, hz, htotal⟩ := hr.1
    exact htotal ▸ h z hz

abbrev V := Fin 10

def edges : EdgeSet 10 :=
  {(0,7), (0,8), (0,9), (1,2), (1,3), (1,4), (1,8), (1,9),
   (2,3), (3,9), (4,5), (4,6), (4,8), (4,9), (5,6), (5,9), (7,8), (7,9)}

/-- Check the short graph6 header, the 45 column-major adjacency bits, and zero padding. -/
private def graphCode := "IJOG[BHvO".toList.map (fun c => c.toNat - 63)

private def payloadBit (position : ℕ) : Bool :=
  (graphCode.getD (1 + position / 6) 0).testBit (5 - position % 6)

theorem graph6_certificate :
    graphCode.head? = some 10 ∧ graphCode.length = 9 ∧
    (∀ i : Fin 3, payloadBit (45 + i.val) = false) ∧
    ∀ u v : V, (u, v) ∈ edges ↔
      u < v ∧ payloadBit (v.val * (v.val - 1) / 2 + u.val) = true := by
  decide +kernel

noncomputable def x (v : V) : ℝ := if v = 9 then 6 else 0

def A : Finset V := {1,2,3,9}
def B : Finset V := {4,5,6,9}
def C : Finset V := {0,7,8,9}
def T : Finset V := {0,7,8}

-- Both inequalities are checked by kernel reduction on the finite powerset.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem expansion_cert : ∀ S : Finset V, S.card ≤ 5 →
    4 * S.card ≤ 3 * cutSize edges S := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem hub_cert : ∀ S : Finset V, S.card ≤ 5 → (9 : V) ∈ S →
    6 ≤ cutSize edges S := by decide +kernel

-- A finite conjunction can be decided directly without unfolding the real field.
theorem edges_ordered : OrderedEdges edges := by
  unfold OrderedEdges
  decide +kernel

theorem edge_count : edges.card = 18 := by decide +kernel

private def Adj (u v : V) : Prop := (u, v) ∈ edges ∨ (v, u) ∈ edges

/-- Explicit connectivity certificate: each vertex has a path of length at most two to 9. -/
theorem paths_to_hub : ∀ v : V,
    v = 9 ∨ Adj v 9 ∨ ∃ w : V, Adj v w ∧ Adj w 9 := by
  unfold Adj
  decide +kernel

theorem tight_A : A.card ≤ 5 ∧ cutSize edges A = 6 ∧ (9 : V) ∈ A := by
  decide +kernel

theorem tight_B : B.card ≤ 5 ∧ cutSize edges B = 6 ∧ (9 : V) ∈ B := by
  decide +kernel

theorem tight_C : C.card ≤ 5 ∧ cutSize edges C = 6 ∧ (9 : V) ∈ C := by
  decide +kernel

theorem cover_cert : ∀ v : V, v ∈ A ∨ v ∈ B ∨ v ∈ C := by decide +kernel

theorem T_cert : T.card = 3 ∧ cutSize edges T = 4 := by decide +kernel

/-- The witness vector assigns all its mass to vertex 9. -/
theorem sum_x (S : Finset V) :
    (∑ v ∈ S, x v) = if (9 : V) ∈ S then 6 else 0 := by
  classical
  simp [x]

theorem x_feasible : Feasible edges x := by
  constructor
  · intro v
    unfold x
    split <;> norm_num
  · intro S hS
    change S.card ≤ 5 at hS
    rw [sum_x]
    by_cases h9 : (9 : V) ∈ S
    · rw [if_pos h9]
      exact_mod_cast (hub_cert S hS h9)
    · rw [if_neg h9]
      exact Nat.cast_nonneg _

/-- A saturated admissible constraint forces equality on each of its coordinates
for any feasible real vector dominating x. -/
theorem tight_coordinate (S : Finset V) (hs : S.card ≤ 5)
    (ht : cutSize edges S = 6) (h9 : (9 : V) ∈ S)
    (y : V → ℝ) (hy : Feasible edges y) (hd : ∀ v, x v ≤ y v)
    (v : V) (hv : v ∈ S) : y v = x v := by
  have hsum := hy.2 S (show S.card ≤ 10 / 2 from hs)
  rw [ht] at hsum
  norm_num at hsum
  have hx : (∑ i ∈ S, x i) = 6 := by rw [sum_x, if_pos h9]
  have hn : ∀ i ∈ S, 0 ≤ y i - x i := by
    intro i _
    exact sub_nonneg.mpr (hd i)
  have hle : y v - x v ≤ ∑ i ∈ S, (y i - x i) :=
    Finset.single_le_sum hn hv
  rw [Finset.sum_sub_distrib, hx] at hle
  exact le_antisymm (by linarith only [hle, hsum]) (hd v)

theorem x_pareto : Pareto edges x := by
  refine ⟨x_feasible, ?_⟩
  intro y hy hd
  funext v
  rcases cover_cert v with ha | hb | hc
  · exact tight_coordinate A tight_A.1 tight_A.2.1 tight_A.2.2 y hy hd v ha
  · exact tight_coordinate B tight_B.1 tight_B.2.1 tight_B.2.2 y hy hd v hb
  · exact tight_coordinate C tight_C.1 tight_C.2.1 tight_C.2.2 y hy hd v hc

theorem cheeger_exact : IsCheeger edges (4 / 3 : ℝ) := by
  constructor
  · intro S _ hS
    change S.card ≤ 5 at hS
    have hn := expansion_cert S hS
    have hr : (4 : ℝ) * (S.card : ℝ) ≤ 3 * (cutSize edges S : ℝ) := by
      exact_mod_cast hn
    linarith
  · refine ⟨T, ?_, ?_, ?_⟩
    · rw [T_cert.1]; decide
    · rw [T_cert.1]; decide
    · rw [T_cert.1, T_cert.2]; norm_num

theorem total_mass : (∑ v : V, x v) = 6 := by
  simpa only [Finset.mem_univ, if_true] using (sum_x Finset.univ)

/-- If all admissible cuts containing u have capacity at least b, a Pareto vector
has total mass at least b. Otherwise the missing mass can be added at u. -/
theorem pareto_mass_ge {n : ℕ} {E : EdgeSet n} {z : Fin n → ℝ}
    (hz : Pareto E z) (u : Fin n) {b : ℝ}
    (hb : ∀ S : Finset (Fin n), S.card ≤ n / 2 → u ∈ S → b ≤ (cutSize E S : ℝ)) :
    b ≤ ∑ v, z v := by
  classical
  by_contra! h
  let d := b - ∑ v, z v
  have hd : 0 < d := sub_pos.mpr h
  let y (v : Fin n) := z v + if v = u then d else 0
  have hdom (v : Fin n) : z v ≤ y v := by
    by_cases hv : v = u <;> simp [y, hv, hd.le]
  have hy : Feasible E y := by
    refine ⟨fun v => (hz.1.1 v).trans (hdom v), ?_⟩
    intro S hs
    by_cases hu : u ∈ S
    · calc
        ∑ v ∈ S, y v = (∑ v ∈ S, z v) + d := by
          simp [y, Finset.sum_add_distrib, hu]
        _ ≤ (∑ v, z v) + d := add_le_add_right (Finset.sum_le_univ_sum_of_nonneg hz.1.1) _
        _ = b := by dsimp [d]; linarith
        _ ≤ _ := hb S hs hu
    · simpa [y, Finset.sum_add_distrib, hu] using hz.1.2 S hs
  have heq := congrFun (hz.2 y hy hdom) u
  have : z u + d = z u := by simpa [y] using heq
  linarith

/-- The minimum in the original question is attained and is exactly six. -/
theorem rho_exact : IsLeast {t : ℝ | ∃ z, Pareto edges z ∧ (∑ v, z v) = t} 6 := by
  refine ⟨⟨x, x_pareto, total_mass⟩, ?_⟩
  rintro t ⟨z, hz, rfl⟩
  apply pareto_mass_ge hz (9 : V)
  intro S hs hu
  exact_mod_cast hub_cert S hs hu

theorem counterexample :
    OrderedEdges edges ∧ IsCheeger edges (4 / 3 : ℝ) ∧ Pareto edges x ∧
      (∑ v : V, x v) < ((10 / 2 : ℕ) : ℝ) * (4 / 3 : ℝ) := by
  refine ⟨edges_ordered, cheeger_exact, x_pareto, ?_⟩
  rw [total_mass]
  norm_num

/-- The final theorem refutes the general conjecture, not a restricted class of
vectors or a finite approximation to the conjecture. -/
theorem not_conjectureB : ¬ ConjectureB := by
  intro h
  have hb := h 10 edges (by decide) edges_ordered (4 / 3 : ℝ)
    cheeger_exact x x_pareto
  exact (not_lt_of_ge hb) counterexample.2.2.2

#print axioms graph6_certificate
#print axioms rho_exact
#print axioms not_conjectureB

end CheegerPareto
