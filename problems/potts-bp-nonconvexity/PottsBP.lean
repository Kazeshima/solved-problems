import Mathlib

/-!
Counterexample to Liu–Mani–Pernice, arXiv:2411.06541v2, Question 4.
All probabilities are real, including boundary points of the simplex.
The special instance has q = 4, d = 2, beta = 1/2.
The configuration-sum interpretation is proved in PottsBPSource.
-/

namespace PottsBP

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

abbrev V := Fin 4 → ℝ

def simplex (p : V) : Prop :=
  (∀ i, 0 ≤ p i) ∧ p 0 + p 1 + p 2 + p 3 = 1

-- Four times the unnormalized BP weight, at beta = 1/2.
noncomputable def weight (p r : V) (i : Fin 4) : ℝ :=
  (2 - p i) * (2 - r i)

noncomputable def partition (p r : V) : ℝ :=
  weight p r 0 + weight p r 1 + weight p r 2 + weight p r 3

noncomputable def bp (p r : V) : V := fun i => weight p r i / partition p r

def prodImage : Set V := {x | ∃ p r, simplex p ∧ simplex r ∧ bp p r = x}

noncomputable def u : V := ![1/6, 1/6, 1/3, 1/3]
noncomputable def v : V := ![1/4, 1/4, 1/6, 1/3]
noncomputable def w : V := ![5/24, 5/24, 1/4, 1/3]

lemma coord_le_one (p : V) (hp : simplex p) (i : Fin 4) : p i ≤ 1 := by
  obtain ⟨h, hs⟩ := hp
  calc
    p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
    _ = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hs

lemma weight_pos (p r : V) (hp : simplex p) (hr : simplex r) (i : Fin 4) :
    0 < weight p r i := by
  unfold weight
  exact mul_pos (by linarith [coord_le_one p hp i])
    (by linarith [coord_le_one r hr i])

lemma partition_pos (p r : V) (hp : simplex p) (hr : simplex r) :
    0 < partition p r := by
  unfold partition
  linarith [weight_pos p r hp hr 0, weight_pos p r hp hr 1,
    weight_pos p r hp hr 2, weight_pos p r hp hr 3]

lemma u_mem : u ∈ prodImage := by
  change ∃ p r, simplex p ∧ simplex r ∧ bp p r = u
  refine ⟨![1, 0, 0, 0], ![0, 1, 0, 0], ?_, ?_, ?_⟩
  · constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num
  · constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num
  · funext i
    fin_cases i <;> norm_num [bp, weight, partition, u]

lemma v_mem : v ∈ prodImage := by
  change ∃ p r, simplex p ∧ simplex r ∧ bp p r = v
  refine ⟨![0, 0, 1, 0], ![1/2, 1/2, 0, 0], ?_, ?_, ?_⟩
  · constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num
  · constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num
  · funext i
    fin_cases i <;> norm_num [bp, weight, partition, v]

lemma w_not_mem : w ∉ prodImage := by
  intro hw
  change ∃ p r, simplex p ∧ simplex r ∧ bp p r = w at hw
  obtain ⟨p, r, hp, hr, heq⟩ := hw
  have hZ := partition_pos p r hp hr
  have hp3_le := coord_le_one p hp 3
  obtain ⟨hp, hs⟩ := hp
  obtain ⟨hr, ht⟩ := hr
  have hwgt (i : Fin 4) : weight p r i = w i * partition p r := by
    have h := congrFun heq i
    change weight p r i / partition p r = w i at h
    exact (div_eq_iff (ne_of_gt hZ)).mp h
  have h0 : weight p r 0 = (5/24 : ℝ) * partition p r := by
    simpa [w] using hwgt 0
  have h1 : weight p r 1 = (5/24 : ℝ) * partition p r := by
    simpa [w] using hwgt 1
  have h2 : weight p r 2 = (1/4 : ℝ) * partition p r := by
    simpa [w] using hwgt 2
  have h3 : weight p r 3 = (1/3 : ℝ) * partition p r := by
    simpa [w] using hwgt 3
  have hface : weight p r 0 + weight p r 1 + weight p r 2 - 2 * weight p r 3 = 0 := by
    linarith [h0, h1, h2, h3]
  have hid : weight p r 0 + weight p r 1 + weight p r 2 - 2 * weight p r 3 =
      6 * p 3 + (6 - 2 * p 3) * r 3 + p 0 * r 0 + p 1 * r 1 + p 2 * r 2 := by
    unfold weight
    nlinarith only [hs, ht]
  rw [hid] at hface
  have hA : 0 ≤ 6 * p 3 := by linarith [hp 3]
  have hB : 0 ≤ (6 - 2 * p 3) * r 3 := mul_nonneg (by linarith) (hr 3)
  have hC : 0 ≤ p 0 * r 0 := mul_nonneg (hp 0) (hr 0)
  have hD : 0 ≤ p 1 * r 1 := mul_nonneg (hp 1) (hr 1)
  have hE : 0 ≤ p 2 * r 2 := mul_nonneg (hp 2) (hr 2)
  have hp3z : p 3 = 0 := by linarith [hp 3]
  have hr3z : r 3 = 0 := by
    rw [hp3z] at hface
    norm_num at hface
    linarith [hr 3]
  have hz0 : p 0 * r 0 = 0 := by linarith
  have hz1 : p 1 * r 1 = 0 := by linarith
  have hz2 : p 2 * r 2 = 0 := by linarith
  have hw3 : weight p r 3 = 4 := by norm_num [weight, hp3z, hr3z]
  have hZ12 : partition p r = 12 := by linarith [h3, hw3]
  rw [hZ12] at h0 h1 h2
  norm_num at h0 h1 h2
  unfold weight at h0 h1 h2
  have hsum0 : p 0 + r 0 = 3/4 := by nlinarith only [h0, hz0]
  have hsum1 : p 1 + r 1 = 3/4 := by nlinarith only [h1, hz1]
  have hsum2 : p 2 + r 2 = 1/2 := by nlinarith only [h2, hz2]
  have hc0 : p 0 = 0 ∨ p 0 = 3/4 := by
    rcases mul_eq_zero.mp hz0 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hc1 : p 1 = 0 ∨ p 1 = 3/4 := by
    rcases mul_eq_zero.mp hz1 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hc2 : p 2 = 0 ∨ p 2 = 1/2 := by
    rcases mul_eq_zero.mp hz2 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hc0 with h0' | h0' <;> rcases hc1 with h1' | h1' <;>
    rcases hc2 with h2' | h2' <;> linarith only [h0', h1', h2', hs, hp3z]

lemma midpoint_eq : (1/2 : ℝ) • u + (1/2 : ℝ) • v = w := by
  funext i
  fin_cases i <;> norm_num [u, v, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem not_convex : ¬ Convex ℝ prodImage := by
  intro h
  have hm := h u_mem v_mem (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  rw [midpoint_eq] at hm
  exact w_not_mem hm

-- The precise finite-dimensional model with arbitrary q, d and beta.
open scoped BigOperators

def simplexN {q : ℕ} (p : Fin q → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

noncomputable def rawWeight {q d : ℕ} (β : ℝ) (p : Fin d → Fin q → ℝ)
    (i : Fin q) : ℝ := ∏ j, (1 - (1 - β) * p j i)

noncomputable def generalBP {q d : ℕ} (β : ℝ) (p : Fin d → Fin q → ℝ) : Fin q → ℝ :=
  fun i => rawWeight β p i / (∑ k, rawWeight β p k)

def generalImage (q d : ℕ) (β : ℝ) : Set (Fin q → ℝ) :=
  {x | ∃ p : Fin d → Fin q → ℝ,
    (∀ j, simplexN (p j)) ∧ (0 < ∑ k, rawWeight β p k) ∧ generalBP β p = x}

lemma simplexN_four (p : V) : simplexN p ↔ simplex p := by
  simp [simplexN, simplex, Fin.sum_univ_succ, add_assoc]

lemma rawWeight_four (p : Fin 2 → V) (i : Fin 4) :
    rawWeight (1/2 : ℝ) p i = weight (p 0) (p 1) i / 4 := by
  simp [rawWeight, weight, Fin.prod_univ_succ]
  ring

lemma rawPartition_four (p : Fin 2 → V) :
    (∑ k, rawWeight (1/2 : ℝ) p k) = partition (p 0) (p 1) / 4 := by
  calc
    _ = ∑ k, weight (p 0) (p 1) k / 4 := Finset.sum_congr rfl fun k _ => rawWeight_four p k
    _ = _ := by simp [partition, Fin.sum_univ_succ]; ring

lemma generalBP_four (p : Fin 2 → V) :
    generalBP (1/2 : ℝ) p = bp (p 0) (p 1) := by
  funext i
  unfold generalBP bp
  rw [rawWeight_four, rawPartition_four]
  -- Division by the same nonzero scaling factor cancels, even at zero total.
  by_cases hz : partition (p 0) (p 1) = 0
  · simp [hz]
  · field_simp [hz]

lemma generalImage_four : generalImage 4 2 (1/2 : ℝ) = prodImage := by
  ext x
  constructor
  · intro hx
    change ∃ p : Fin 2 → V, (∀ j, simplexN (p j)) ∧
      (0 < ∑ k, rawWeight (1/2 : ℝ) p k) ∧ generalBP (1/2 : ℝ) p = x at hx
    obtain ⟨p, hp, _, hx⟩ := hx
    change ∃ p r, simplex p ∧ simplex r ∧ bp p r = x
    exact ⟨p 0, p 1, (simplexN_four _).mp (hp 0), (simplexN_four _).mp (hp 1),
      (generalBP_four p).symm.trans hx⟩
  · intro hx
    change ∃ p r, simplex p ∧ simplex r ∧ bp p r = x at hx
    obtain ⟨p, r, hp, hr, hx⟩ := hx
    let z : Fin 2 → V := ![p, r]
    have hz0 : z 0 = p := by rfl
    have hz1 : z 1 = r := by rfl
    change ∃ p : Fin 2 → V, (∀ j, simplexN (p j)) ∧
      (0 < ∑ k, rawWeight (1/2 : ℝ) p k) ∧ generalBP (1/2 : ℝ) p = x
    refine ⟨z, ?_, ?_, ?_⟩
    · intro j
      fin_cases j
      · exact (simplexN_four p).mpr hp
      · exact (simplexN_four r).mpr hr
    · rw [rawPartition_four, hz0, hz1]
      exact div_pos (partition_pos p r hp hr) (by norm_num)
    · rw [generalBP_four, hz0, hz1]
      exact hx

-- Universal positive answer to Question 4 (d >= 2 is enough to refute it).
def Question4 : Prop := ∀ (q d : ℕ) (β : ℝ),
  3 ≤ q → 2 ≤ d → max 0 (1 - (q : ℝ) / ((d : ℝ) + 1)) ≤ β → β ≤ 1 →
  Convex ℝ (generalImage q d β)

theorem question4_counterexample : ¬ Convex ℝ (generalImage 4 2 (1/2 : ℝ)) := by
  rw [generalImage_four]
  exact not_convex

theorem question4_false : ¬ Question4 := by
  intro h
  apply question4_counterexample
  exact h 4 2 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms question4_false

end PottsBP
