import CheegerTen.Exclusion
import CheegerTen.Models

/-! Exact real-vector results and nonisomorphism for the order-ten survivors. -/
namespace CheegerPareto.Ten

open scoped BigOperators

theorem expansion (i : Model) : IsCheeger (edgesOf i) ((numerator i : ℝ) / 3) := by
  constructor
  · intro s _ hs
    have : (numerator i : ℝ) * (s.card : ℝ) ≤ 3 * (cutSize (edgesOf i) s : ℝ) := by
      exact_mod_cast (small_cuts i s hs).1
    linarith
  · refine ⟨row, ?_, ?_, ?_⟩
    · rw [(attainment i).1]; decide
    · rw [(attainment i).1]; decide
    · rw [(attainment i).1, (attainment i).2]
      simpa only [Nat.cast_ofNat] using
        div_mul_cancel₀ (numerator i : ℝ) (by norm_num : (3 : ℝ) ≠ 0)

theorem efficient (i : Model) : Pareto (edgesOf i) (weight i) := by
  classical
  have sumOn (s : Finset V) : (∑ v ∈ s, weight i v) =
      if (9 : V) ∈ s then (mass i : ℝ) else 0 := by simp [weight]
  constructor
  · constructor
    · intro v; by_cases hv : v = 9 <;> simp [weight, hv]
    · intro s hs
      rw [sumOn]
      split
      next h => exact_mod_cast (small_cuts i s hs).2 h
      next => exact Nat.cast_nonneg _
  · intro y hy hd
    funext v
    obtain ⟨s, _, hv, h9, hs, hc⟩ := covering i v
    have hsum := hy.2 s hs
    rw [hc] at hsum
    have hone : y v - weight i v ≤ ∑ w ∈ s, (y w - weight i w) :=
      Finset.single_le_sum (fun w _ => sub_nonneg.mpr (hd w)) hv
    rw [Finset.sum_sub_distrib, sumOn, if_pos h9] at hone
    exact le_antisymm (by linarith only [hone, hsum]) (hd v)

theorem total (i : Model) : (∑ v, weight i v) = mass i := by simp [weight]

theorem efficient_minima (i : Model) :
    IsLeast {w : ℝ | ∃ z, Pareto (edgesOf i) z ∧ (∑ v, z v) = w} (mass i : ℝ) := by
  refine ⟨⟨weight i, efficient i, total i⟩, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  apply pareto_mass_ge hz (9 : V)
  intro s hs hu
  exact_mod_cast (small_cuts i s hs).2 hu

def Violates (E : EdgeSet 10) : Prop :=
  OrderedEdges E ∧ ∃ (h : ℝ) (z : V → ℝ),
    IsCheeger E h ∧ Pareto E z ∧ (∑ v, z v) < 5 * h

theorem violations (i : Model) : Violates (edgesOf i) := by
  refine ⟨ordered i, (numerator i : ℝ) / 3, weight i, expansion i, efficient i, ?_⟩
  rw [total]
  have gap : 3 * mass i < 5 * numerator i := by fin_cases i <;> decide +kernel
  have hr : (3 : ℝ) * mass i < 5 * (numerator i : ℝ) := by exact_mod_cast gap
  linarith

abbrev Adj (E : EdgeSet 10) (a b : V) : Prop := (a,b) ∈ E ∨ (b,a) ∈ E
def degree (E : EdgeSet 10) (a : V) := (Finset.univ.filter (Adj E a)).card

theorem paths (i : Model) : ∀ v : V,
    v = 9 ∨ Adj (edgesOf i) v 9 ∨ ∃ w : V, Adj (edgesOf i) v w ∧ Adj (edgesOf i) w 9 := by
  fin_cases i <;> decide +kernel

def Connected (E : EdgeSet 10) : Prop := ∀ u v, Relation.ReflTransGen (Adj E) u v

theorem connected (i : Model) : Connected (edgesOf i) := by
  have hub (v : V) : Relation.ReflTransGen (Adj (edgesOf i)) v 9 := by
    rcases paths i v with h | h | ⟨w, hw, h9⟩
    · subst v; exact .refl
    · exact .single h
    · exact (Relation.ReflTransGen.single hw).tail h9
  have sym : Symmetric (Adj (edgesOf i)) := fun _ _ h => h.elim Or.inr Or.inl
  intro u v
  exact (hub u).trans (Relation.ReflTransGen.symmetric sym (hub v))

def Isomorphic (E F : EdgeSet 10) : Prop :=
  ∃ f : V ≃ V, ∀ a b, Adj E a b ↔ Adj F (f a) (f b)

private theorem degree_preserved {E F : EdgeSet 10} (f : V ≃ V)
    (he : ∀ a b, Adj E a b ↔ Adj F (f a) (f b)) (a : V) : degree E a = degree F (f a) := by
  have eq : (Finset.univ.filter (Adj E a)).map f.toEmbedding =
      Finset.univ.filter (Adj F (f a)) := by
    ext v
    obtain ⟨w, rfl⟩ := f.surjective v
    simpa using he a w
  unfold degree
  rw [← eq, Finset.card_map]

private theorem no_degree_four : ∀ v : V, degree (edgesOf 0) v ≠ 4 := by decide +kernel
private theorem degree_four : degree (edgesOf 1) 8 = 4 := by decide +kernel

theorem distinct_eighteen : ¬ Isomorphic (edgesOf 0) (edgesOf 1) := by
  rintro ⟨f, he⟩
  obtain ⟨u, hu⟩ := f.surjective 8
  have hd := degree_preserved f he u
  rw [hu, degree_four] at hd
  exact no_degree_four u hd

theorem distinct_universal (i : Model) (hi : i ≠ 2) : ¬ Isomorphic (edgesOf i) (edgesOf 2) := by
  have low : ∀ j : Model, j ≠ 2 → ∀ v : V, degree (edgesOf j) v ≠ 9 := by decide +kernel
  have high : degree (edgesOf 2) 9 = 9 := by decide +kernel
  rintro ⟨f, he⟩
  obtain ⟨v, h⟩ := f.surjective 9
  exact low i hi v (by simpa [h, high] using degree_preserved f he v)

def relabel (v : V) : V := ([2,7,4,1,0,3,6,5,8,9] : List V).getD v.val 0

theorem original_relabels : Isomorphic edges (edgesOf 1) := by
  have hb : Function.Bijective relabel := by
    unfold Function.Bijective Function.Injective Function.Surjective
    decide +kernel
  have he : ∀ a b, Adj edges a b ↔ Adj (edgesOf 1) (relabel a) (relabel b) := by decide +kernel
  exact ⟨Equiv.ofBijective relabel hb, he⟩

/-- Nonuniqueness already holds among connected order-ten graphs with eighteen edges. -/
theorem nonunique_at_eighteen :
    ∃ E F : EdgeSet 10, E.card = 18 ∧ F.card = 18 ∧ Connected E ∧ Connected F ∧
      Violates E ∧ Violates F ∧ ¬ Isomorphic E F := by
  exact ⟨edgesOf 0, edgesOf 1, by simpa using edge_counts 0, by simpa using edge_counts 1,
    connected 0, connected 1, violations 0, violations 1, distinct_eighteen⟩

#print axioms excluded_by_search
#print axioms excluded_by_tree
#print axioms efficient_minima
#print axioms original_relabels
#print axioms nonunique_at_eighteen

run_cmd do
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  for target in #[``excluded_by_tree, ``violations, ``efficient_minima, ``original_relabels,
      ``nonunique_at_eighteen] do
    let actual ← Lean.collectAxioms target
    unless actual.all expected.contains && expected.all actual.contains do
      throwError "Unexpected standard axiom set for {target}: {actual}"

end CheegerPareto.Ten
