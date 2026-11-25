import CheegerMinimum.Analytic
import CheegerMinimum.Covers

/-! The minimum counterexample order for the floor-corrected conjecture. -/
namespace CheegerPareto

open scoped BigOperators

/-- Every feasible Pareto-maximal real vector satisfies B through order nine. -/
theorem bound_through_nine {n : ℕ} (lo : 2 ≤ n) (hi : n ≤ 9)
    {E : EdgeSet n} {h : ℝ} (hh : IsCheeger E h) {z : Fin n → ℝ} (hz : Pareto E z) :
    ((n / 2 : ℕ) : ℝ) * h ≤ ∑ v, z v := by
  by_contra! bad
  exact Small.no_small_cover lo hi (Small.MaxTight E z) (Small.maxTight_at lo hz)
    (fun _ gs => Small.tight_card_lt hh hz.1 bad gs.1)
    (fun _ _ gs gt hst => Small.maxTight_pair hh hz.1 bad gs gt hst)

def CounterexampleOrder (n : ℕ) : Prop :=
  2 ≤ n ∧ ∃ (E : EdgeSet n) (h : ℝ) (z : Fin n → ℝ),
    OrderedEdges E ∧ IsCheeger E h ∧ Pareto E z ∧
    (∑ v, z v) < ((n / 2 : ℕ) : ℝ) * h

/-- Least order among all finite simple graphs and all real efficient vectors. -/
theorem minimum_counterexample_order : IsLeast {n : ℕ | CounterexampleOrder n} 10 := by
  constructor
  · exact ⟨by decide, edges, 4 / 3, x, counterexample⟩
  · rintro n ⟨hn, E, h, z, _, hh, hz, hbad⟩
    by_contra! hlt
    exact (not_lt_of_ge (bound_through_nine hn (by omega) hh hz)) hbad

#print axioms bound_through_nine
#print axioms minimum_counterexample_order

run_cmd do
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  for target in #[``bound_through_nine, ``minimum_counterexample_order] do
    let actual ← Lean.collectAxioms target
    unless actual.all expected.contains && expected.all actual.contains do
      throwError "Unexpected axiom set for {target}: {actual}"

end CheegerPareto
