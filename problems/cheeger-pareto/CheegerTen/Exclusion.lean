import CheegerMinimum

/-! A sound, integer-only exclusion test for any ten-vertex graph and any
nonempty admissible reference cut. -/
namespace CheegerPareto.Ten

open scoped BigOperators

def pool (E : EdgeSet 10) (t : Finset V) : Finset (Finset V) :=
  Finset.univ.filter fun a : Finset V =>
    3 ≤ a.card ∧ a.card ≤ 4 ∧ t.card * cutSize E a < 5 * cutSize E t

abbrev PairOK (E : EdgeSet 10) (t a b : Finset V) : Prop :=
  (a ∩ b).Nonempty ∧ 5 < (a ∪ b).card ∧
  t.card * (cutSize E a + cutSize E b) < 5 * cutSize E t + t.card * cutSize E (a ∩ b)

/-- Select a tight set through the least remaining vertex and restrict subsequent
choices to compatible sets. The fuel decreases with the number of uncovered vertices. -/
def search (E : EdgeSet 10) (t : Finset V) :
    ℕ → Finset V → Finset (Finset V) → Bool
  | 0, rest, _ => decide (rest = ∅)
  | fuel + 1, rest, choices =>
    if hn : rest.Nonempty then
      decide (∃ a ∈ choices, rest.min' hn ∈ a ∧
        search E t fuel (rest \ a) (choices.filter (PairOK E t a)) = true)
    else true

private theorem search_complete (E : EdgeSet 10) (t : Finset V) (good : Finset V → Prop)
    (pairs : ∀ a b, good a → good b → a ≠ b → PairOK E t a b)
    (fuel : ℕ) (rest : Finset V) (choices : Finset (Finset V)) (bound : rest.card ≤ fuel)
    (covered : ∀ v ∈ rest, ∃ a ∈ choices, good a ∧ v ∈ a) :
    search E t fuel rest choices = true := by
  induction fuel generalizing rest choices with
  | zero =>
    have he : rest = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [search, he]
  | succ fuel ih =>
    rw [search]
    split
    next hn =>
      let v := rest.min' hn
      have hv : v ∈ rest := rest.min'_mem hn
      obtain ⟨a, ha, ga, hva⟩ := covered v hv
      apply decide_eq_true
      refine ⟨a, ha, hva, ih _ _ ?_ ?_⟩
      · have sub : rest \ a ⊂ rest :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun he =>
            (Finset.mem_sdiff.mp (he.symm ▸ hv)).2 hva⟩
        have := Finset.card_lt_card sub
        omega
      · intro w hw
        obtain ⟨wr, wa⟩ := Finset.mem_sdiff.mp hw
        obtain ⟨b, hb, gb, wb⟩ := covered w wr
        exact ⟨b, Finset.mem_filter.mpr ⟨hb, pairs a b ga gb (fun he => wa (he ▸ wb))⟩, gb, wb⟩
    next => rfl

private theorem cover_of_violation {E : EdgeSet 10} {h : ℝ} (hh : IsCheeger E h)
    {z : V → ℝ} (hz : Pareto E z) (bad : (∑ v, z v) < 5 * h)
    (t : Finset V) (ht0 : 0 < t.card) (ht5 : t.card ≤ 5) :
    (∀ v : V, ∃ a ∈ pool E t, Small.MaxTight E z a ∧ v ∈ a) ∧
    (∀ a b, Small.MaxTight E z a → Small.MaxTight E z b → a ≠ b → PairOK E t a b) := by
  classical
  have hb : (∑ v, z v) < ((10 / 2 : ℕ) : ℝ) * h := by simpa using bad
  have hpos : 0 < (t.card : ℝ) := by exact_mod_cast ht0
  have level : (t.card : ℝ) * (∑ v, z v) < 5 * (cutSize E t : ℝ) := by
    have upper := hh.1 t ht0 ht5
    have strict := mul_lt_mul_of_pos_left bad hpos
    nlinarith only [upper, strict]
  constructor
  · intro v
    obtain ⟨a, ga, va⟩ := Small.maxTight_at (by decide) hz v
    have small : a.card < 5 := Small.tight_card_lt hh hz.1 hb ga.1
    obtain ⟨w, hw⟩ := Finset.sdiff_nonempty_of_card_lt_card
      (s := a) (t := Finset.univ) (by simp; omega)
    obtain ⟨b, gb, wb⟩ := Small.maxTight_at (by decide) hz w
    have ab : a ≠ b := fun he => (Finset.mem_sdiff.mp hw).2 (he ▸ wb)
    obtain ⟨big, meet, _⟩ := Small.maxTight_pair hh hz.1 hb ga gb ab
    have bsmall : b.card < 5 := Small.tight_card_lt hh hz.1 hb gb.1
    have hp := Finset.card_pos.mpr meet
    have eq := Finset.card_union_add_card_inter a b
    change 5 < (a ∪ b).card at big
    have c : (cutSize E a : ℝ) ≤ ∑ v, z v :=
      ga.1.2.symm.le.trans (Finset.sum_le_univ_sum_of_nonneg hz.1.1)
    have cl := lt_of_le_of_lt (mul_le_mul_of_nonneg_left c hpos.le) level
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by omega, ?_⟩, ga, va⟩
    exact_mod_cast cl
  · intro a b ga gb ab
    obtain ⟨big, meet, _⟩ := Small.maxTight_pair hh hz.1 hb ga gb ab
    have cap := hz.1.2 (a ∩ b) ((Finset.card_le_card Finset.inter_subset_left).trans ga.1.1)
    have mass : (∑ v ∈ a ∪ b, z v) ≤ ∑ v, z v := Finset.sum_le_univ_sum_of_nonneg hz.1.1
    have sums : (∑ v ∈ a ∪ b, z v) + (∑ v ∈ a ∩ b, z v) =
        (∑ v ∈ a, z v) + ∑ v ∈ b, z v := Finset.sum_union_inter
    have bound : (cutSize E a : ℝ) + cutSize E b ≤ (∑ v, z v) + cutSize E (a ∩ b) := by
      linarith only [cap, mass, sums, ga.1.2, gb.1.2]
    have prod := mul_le_mul_of_nonneg_left bound hpos.le
    rw [mul_add (t.card : ℝ) (∑ v, z v)] at prod
    have cert := lt_of_le_of_lt prod (add_lt_add_right level ((t.card : ℝ) * cutSize E (a ∩ b)))
    exact ⟨meet, big, by exact_mod_cast cert⟩

/-- A violating real vector forces the integer search to succeed. An attaining
reference cut gives the threshold used in the census, but any reference cut suffices. -/
theorem violation_passes {E : EdgeSet 10} {h : ℝ} (hh : IsCheeger E h)
    {z : V → ℝ} (hz : Pareto E z) (bad : (∑ v, z v) < 5 * h)
    (t : Finset V) (ht0 : 0 < t.card) (ht5 : t.card ≤ 5) :
    search E t 10 Finset.univ (pool E t) = true := by
  obtain ⟨covered, pairs⟩ := cover_of_violation hh hz bad t ht0 ht5
  exact search_complete E t (Small.MaxTight E z) pairs 10 _ _ (by simp) (fun v _ => covered v)

/-- Each tree node supplies a still-uncovered vertex. All candidate sets
through it require a child. A vertex with no available set closes the branch. -/
inductive Refutation (E : EdgeSet 10) (t : Finset V) :
    Finset V → Finset (Finset V) → Prop where
  | node {rest choices} (v : V) (hv : v ∈ rest)
      (children : ∀ a ∈ choices, v ∈ a → Refutation E t (rest \ a)
        (choices.filter fun b => ((rest \ a) ∩ b).Nonempty ∧ PairOK E t a b)) :
      Refutation E t rest choices

private theorem refutation_sound {E : EdgeSet 10} {t rest : Finset V}
    {choices : Finset (Finset V)} (tree : Refutation E t rest choices)
    (good : Finset V → Prop) (pairs : ∀ a b, good a → good b → a ≠ b → PairOK E t a b) :
    ¬ (∀ v ∈ rest, ∃ a ∈ choices, good a ∧ v ∈ a) := by
  induction tree with
  | node v hv children ih =>
    intro covered
    obtain ⟨a, ha, ga, va⟩ := covered v hv
    apply ih a ha va
    intro w hw
    obtain ⟨wr, wa⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨b, hb, gb, wb⟩ := covered w wr
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, ⟨w, Finset.mem_inter.mpr ⟨hw, wb⟩⟩,
      pairs a b ga gb (fun eq => wa (eq ▸ wb))⟩, gb, wb⟩

/-- Checking the supplied tree for a graph excludes all real counterexamples on it. -/
theorem excluded_by_tree {E : EdgeSet 10} (t : Finset V) (ht0 : 0 < t.card)
    (ht5 : t.card ≤ 5) (tree : Refutation E t Finset.univ (pool E t))
    {h : ℝ} (hh : IsCheeger E h) {z : V → ℝ} (hz : Pareto E z) : 5 * h ≤ ∑ v, z v := by
  by_contra! bad
  obtain ⟨covered, pairs⟩ := cover_of_violation hh hz bad t ht0 ht5
  exact refutation_sound tree _ pairs (fun v _ => covered v)

theorem excluded_by_search {E : EdgeSet 10} (t : Finset V) (ht0 : 0 < t.card)
    (ht5 : t.card ≤ 5) (certificate : search E t 10 Finset.univ (pool E t) = false)
    {h : ℝ} (hh : IsCheeger E h) {z : V → ℝ} (hz : Pareto E z) :
    5 * h ≤ ∑ v, z v := by
  by_contra! bad
  have := violation_passes hh hz bad t ht0 ht5
  simp [certificate] at this

end CheegerPareto.Ten
