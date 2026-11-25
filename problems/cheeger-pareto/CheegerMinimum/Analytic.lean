import CheegerPareto
import Mathlib.Data.Finset.Max

/-! Necessary conditions on the tight cuts of any underweight real Pareto point. -/
namespace CheegerPareto.Small

open scoped BigOperators
variable {n : ℕ} {E : EdgeSet n} {z : Fin n → ℝ} {h : ℝ}

def Tight (E : EdgeSet n) (z : Fin n → ℝ) (s : Finset (Fin n)) : Prop :=
  s.card ≤ n / 2 ∧ ∑ v ∈ s, z v = (cutSize E s : ℝ)

def MaxTight (E : EdgeSet n) (z : Fin n → ℝ) (s : Finset (Fin n)) : Prop :=
  Tight E z s ∧ ∀ t, Tight E z t → s ⊆ t → s = t

theorem pareto_tight_at (hn : 2 ≤ n) (hz : Pareto E z) (u : Fin n) :
    ∃ s, Tight E z s ∧ u ∈ s := by
  classical
  let pool := Finset.univ.filter fun s : Finset (Fin n) => s.card ≤ n / 2 ∧ u ∈ s
  let slack (s : Finset (Fin n)) : ℝ := cutSize E s - ∑ v ∈ s, z v
  have h1 : 1 ≤ n / 2 := by omega
  have hp : pool.Nonempty := ⟨{u}, by simp [pool, h1]⟩
  obtain ⟨s, hs, low⟩ := pool.exists_min_image slack hp
  obtain ⟨hsSize, hus⟩ := (Finset.mem_filter.mp hs).2
  have nonneg : 0 ≤ slack s := sub_nonneg.mpr (hz.1.2 s hsSize)
  by_cases he : slack s = 0
  · exact ⟨s, ⟨hsSize, (sub_eq_zero.mp he).symm⟩, hus⟩
  · let y (v : Fin n) := z v + if v = u then slack s else 0
    have dominates (v : Fin n) : z v ≤ y v := by
      by_cases hv : v = u <;> simp [y, hv, nonneg]
    have hy : Feasible E y := by
      refine ⟨fun v => (hz.1.1 v).trans (dominates v), ?_⟩
      intro t ht
      by_cases hut : u ∈ t
      · have hl := low t (by simp [pool, ht, hut])
        change slack s ≤ (cutSize E t : ℝ) - ∑ i ∈ t, z i at hl
        simpa [y, Finset.sum_add_distrib, hut] using (le_sub_iff_add_le'.mp hl)
      · simpa [y, Finset.sum_add_distrib, hut] using hz.1.2 t ht
    have eq := congrFun (hz.2 y hy dominates) u
    have : z u + slack s = z u := by simpa [y] using eq
    exact (he (by linarith)).elim

theorem maxTight_at (hn : 2 ≤ n) (hz : Pareto E z) (u : Fin n) :
    ∃ s, MaxTight E z s ∧ u ∈ s := by
  classical
  let pool := Finset.univ.filter fun s : Finset (Fin n) => Tight E z s ∧ u ∈ s
  obtain ⟨a, ha, hua⟩ := pareto_tight_at hn hz u
  obtain ⟨s, hs, largest⟩ := pool.exists_max_image Finset.card
    (show pool.Nonempty from ⟨a, by simp [pool, ha, hua]⟩)
  obtain ⟨hst, hus⟩ := (Finset.mem_filter.mp hs).2
  refine ⟨s, ⟨hst, ?_⟩, hus⟩
  intro t ht hst'
  exact Finset.eq_of_subset_of_card_le hst' (largest t (by simp [pool, ht, hst' hus]))

theorem cut_submodular (E : EdgeSet n) (s t : Finset (Fin n)) :
    cutSize E (s ∪ t) + cutSize E (s ∩ t) ≤ cutSize E s + cutSize E t := by
  simp only [cutSize, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases a : e.1 ∈ s <;> by_cases b : e.2 ∈ s <;>
    by_cases c : e.1 ∈ t <;> by_cases d : e.2 ∈ t <;> simp [a, b, c, d]

theorem cut_complement (E : EdgeSet n) (s : Finset (Fin n)) :
    cutSize E sᶜ = cutSize E s := by
  unfold cutSize
  congr 1
  ext e
  by_cases a : e.1 ∈ s <;> by_cases b : e.2 ∈ s <;> simp [a, b]

private theorem ratio_bound (hh : IsCheeger E h) {s : Finset (Fin n)}
    (hs : s.card ≤ n / 2) : h * s.card ≤ (cutSize E s : ℝ) := by
  by_cases pos : 0 < s.card
  · exact hh.1 s pos hs
  · have : s.card = 0 := by omega
    simp [this]

private theorem expansion_pos (hz : Feasible E z)
    (bad : (∑ v, z v) < ((n / 2 : ℕ) : ℝ) * h) : 0 < h := by
  by_contra! hnon
  exact (not_lt_of_ge (Finset.sum_nonneg (fun v _ => hz.1 v)))
    (lt_of_lt_of_le bad (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hnon))

theorem tight_card_lt (hh : IsCheeger E h) (hz : Feasible E z)
    (bad : (∑ v, z v) < ((n / 2 : ℕ) : ℝ) * h)
    {s : Finset (Fin n)} (hs : Tight E z s) : s.card < n / 2 := by
  by_contra! hn
  have eq := Nat.le_antisymm hs.1 hn
  have hb := ratio_bound hh hs.1
  rw [eq, mul_comm, ← hs.2] at hb
  exact (not_lt_of_ge (hb.trans (Finset.sum_le_univ_sum_of_nonneg hz.1))) bad

/-- Even when the union is too large to be admissible, its boundary is at most
its mass. This follows from submodularity and the feasible intersection. -/
theorem tight_union_bound (hz : Feasible E z) {s t : Finset (Fin n)}
    (hs : Tight E z s) (ht : Tight E z t) :
    (cutSize E (s ∪ t) : ℝ) ≤ ∑ v ∈ s ∪ t, z v := by
  have hsub : (cutSize E (s ∪ t) : ℝ) + cutSize E (s ∩ t) ≤ cutSize E s + cutSize E t := by
    exact_mod_cast cut_submodular E s t
  have hi := hz.2 (s ∩ t) ((Finset.card_le_card Finset.inter_subset_left).trans hs.1)
  have hm : (∑ v ∈ s ∪ t, z v) + (∑ v ∈ s ∩ t, z v) =
      (∑ v ∈ s, z v) + ∑ v ∈ t, z v := Finset.sum_union_inter
  linarith only [hsub, hi, hm, hs.2, ht.2]

theorem maxTight_pair (hh : IsCheeger E h) (hz : Feasible E z)
    (bad : (∑ v, z v) < ((n / 2 : ℕ) : ℝ) * h)
    {s t : Finset (Fin n)} (hs : MaxTight E z s) (ht : MaxTight E z t) (hst : s ≠ t) :
    n / 2 < (s ∪ t).card ∧ (s ∩ t).Nonempty ∧ (s ∪ t).card ≠ n - n / 2 := by
  have hu := tight_union_bound hz hs.1 ht.1
  have htotal : (∑ v ∈ s ∪ t, z v) ≤ ∑ v, z v := Finset.sum_le_univ_sum_of_nonneg hz.1
  have large : n / 2 < (s ∪ t).card := by
    by_contra! small
    have tight : Tight E z (s ∪ t) := ⟨small, le_antisymm (hz.2 _ small) hu⟩
    exact hst ((hs.2 _ tight Finset.subset_union_left).trans
      (ht.2 _ tight Finset.subset_union_right).symm)
  refine ⟨large, ?_, ?_⟩
  · by_contra hnone
    have he : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hd := Finset.disjoint_iff_inter_eq_empty.mpr he
    have hr : ((n / 2 : ℕ) : ℝ) ≤ (s.card : ℝ) + t.card := by
      exact_mod_cast (Finset.card_union_of_disjoint hd ▸ large.le)
    have hsl := ratio_bound hh hs.1.1
    have htl := ratio_bound hh ht.1.1
    rw [← hs.1.2] at hsl
    rw [← ht.1.2] at htl
    rw [Finset.sum_union hd] at htotal
    have hm := mul_le_mul_of_nonneg_left hr (expansion_pos hz bad).le
    rw [mul_add] at hm
    linarith only [bad, hm, hsl, htl, htotal]
  · intro hc
    have hcompl : (s ∪ t)ᶜ.card = n / 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hc]
      omega
    have hlow := ratio_bound hh hcompl.le
    rw [hcompl, cut_complement, mul_comm] at hlow
    exact (not_lt_of_ge (hlow.trans (hu.trans htotal))) bad

end CheegerPareto.Small
