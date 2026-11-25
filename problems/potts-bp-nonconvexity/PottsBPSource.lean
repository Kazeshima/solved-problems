import PottsBP

/-! The finite-configuration interpretation of (1) and (2) in Liu–Mani–Pernice.
The source image has one unrestricted real simplex for each neighbour. -/
namespace PottsBP
open scoped BigOperators
open Finset

def interaction {q : ℕ} (β : ℝ) (i b : Fin q) : ℝ := if i = b then β else 1

noncomputable def productLaw {q d : ℕ} (p : Fin d → Fin q → ℝ) (τ : Fin d → Fin q) : ℝ :=
  ∏ j, p j (τ j)

theorem productLaw_isProbability {q d : ℕ} {p : Fin d → Fin q → ℝ}
    (hp : ∀ j, simplexN (p j)) :
    (∀ τ, 0 ≤ productLaw p τ) ∧ ∑ τ, productLaw p τ = 1 := by
  classical
  constructor
  · exact fun τ => prod_nonneg (fun j _ => (hp j).1 (τ j))
  · simp only [productLaw, ← Fintype.prod_sum, fun j => (hp j).2, prod_const_one]

noncomputable def sourceWeight {q d : ℕ} (β : ℝ) (μ : (Fin d → Fin q) → ℝ)
    (i : Fin q) : ℝ := ∑ τ, μ τ * ∏ j, interaction β i (τ j)

noncomputable def sourceBP {q d : ℕ} (β : ℝ) (μ : (Fin d → Fin q) → ℝ) (i : Fin q) : ℝ :=
  sourceWeight β μ i / ∑ k, sourceWeight β μ k

def sourceImage (q d : ℕ) (β : ℝ) : Set (Fin q → ℝ) :=
  {x | ∃ p : Fin d → Fin q → ℝ, (∀ j, simplexN (p j)) ∧ sourceBP β (productLaw p) = x}

theorem interaction_mean {q : ℕ} (β : ℝ) (p : Fin q → ℝ) (hp : simplexN p) (i : Fin q) :
    (∑ b, p b * interaction β i b) = 1 - (1 - β) * p i := by
  calc
    _ = ∑ b, (p b - (if i = b then (1 - β) * p b else 0)) := by
      apply sum_congr rfl
      intro b _
      by_cases h : i = b
      · simp [interaction, h]
        ring
      · simp [interaction, h]
    _ = _ := by simp [sum_sub_distrib, hp.2]

theorem sourceWeight_eq_rawWeight {q d : ℕ} (β : ℝ) (p : Fin d → Fin q → ℝ)
    (hp : ∀ j, simplexN (p j)) (i : Fin q) :
    sourceWeight β (productLaw p) i = rawWeight β p i := by
  classical
  unfold sourceWeight productLaw rawWeight
  simp only [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j b => p j b * interaction β i b)]
  exact prod_congr rfl fun j _ => interaction_mean β (p j) (hp j) i

theorem sourceBP_eq_generalBP {q d : ℕ} (β : ℝ) (p : Fin d → Fin q → ℝ)
    (hp : ∀ j, simplexN (p j)) : sourceBP β (productLaw p) = generalBP β p := by
  funext i
  simp [sourceBP, generalBP, sourceWeight_eq_rawWeight β p hp]

lemma simplexN_le_one {q : ℕ} {p : Fin q → ℝ} (hp : simplexN p) (i : Fin q) : p i ≤ 1 := by
  rw [← hp.2]
  exact single_le_sum (fun j _ => hp.1 j) (mem_univ i)

lemma product_lower {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hu : (∏ i ∈ s, (1 - f i)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => sub_nonneg.mpr (h1 i)) (fun i _ => by linarith [h0 i])
    nlinarith only [ih, mul_nonneg (h0 a) (sub_nonneg.mpr hu)]

lemma scaled_entry_bounds {q d : ℕ} {β : ℝ} {p : Fin d → Fin q → ℝ}
    (h0 : 0 ≤ β) (h1 : β ≤ 1) (hp : ∀ j, simplexN (p j)) (j : Fin d) (i : Fin q) :
    0 ≤ (1-β) * p j i ∧ (1-β) * p j i ≤ 1 := by
  exact ⟨mul_nonneg (sub_nonneg.mpr h1) ((hp j).1 i),
    mul_le_one₀ (by linarith) ((hp j).1 i) (simplexN_le_one (hp j) i)⟩

lemma sum_linear_weights {q d : ℕ} (β : ℝ) {p : Fin d → Fin q → ℝ}
    (hp : ∀ j, simplexN (p j)) :
    (∑ i, (1 - ∑ j, (1-β) * p j i)) = (q : ℝ) - d * (1-β) := by
  rw [sum_sub_distrib, sum_comm]
  simp [← mul_sum, fun j => (hp j).2]
  ring

theorem partition_lower_bound {q d : ℕ} {β : ℝ} {p : Fin d → Fin q → ℝ}
    (h0 : 0 ≤ β) (h1 : β ≤ 1) (hp : ∀ j, simplexN (p j)) :
    (q : ℝ) - d * (1-β) ≤ ∑ i, rawWeight β p i := by
  rw [← sum_linear_weights β hp]
  exact sum_le_sum fun i _ => product_lower univ _ (fun j => (scaled_entry_bounds h0 h1 hp j i).1)
    (fun j => (scaled_entry_bounds h0 h1 hp j i).2)

theorem admissible_partition_pos {q d : ℕ} {β : ℝ} (hq : 0 < q)
    (hβ : max 0 (1 - (q : ℝ) / (d+1)) ≤ β) (h1 : β ≤ 1)
    {p : Fin d → Fin q → ℝ} (hp : ∀ j, simplexN (p j)) : 0 < ∑ i, rawWeight β p i := by
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : 1 - β ≤ (q : ℝ) / (d+1) := by linarith [(le_max_right 0 _).trans hβ]
  have hmul := (le_div_iff₀ hd).mp ht
  apply lt_of_lt_of_le _ (partition_lower_bound ((le_max_left _ _).trans hβ) h1 hp)
  by_cases hb : β = 1
  · simpa [hb] using hq'
  · nlinarith

theorem sourceImage_eq_generalImage {q d : ℕ} {β : ℝ} (hq : 0 < q)
    (hβ : max 0 (1-(q : ℝ)/(d+1)) ≤ β) (h1 : β ≤ 1) :
    sourceImage q d β = generalImage q d β := by
  ext x
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,admissible_partition_pos hq hβ h1 hp,(sourceBP_eq_generalBP β p hp).symm.trans hx⟩
  · rintro ⟨p,hp,_,hx⟩
    exact ⟨p,hp,(sourceBP_eq_generalBP β p hp).trans hx⟩

theorem source_question4_counterexample : ¬ Convex ℝ (sourceImage 4 2 (1/2 : ℝ)) := by
  rw [sourceImage_eq_generalImage (by norm_num) (by norm_num) (by norm_num)]
  exact question4_counterexample

def SourceQuestion4 : Prop := ∀ (q d : ℕ) (β : ℝ), 3 ≤ q → 2 ≤ d →
  max 0 (1-(q : ℝ)/(d+1)) ≤ β → β ≤ 1 → Convex ℝ (sourceImage q d β)

theorem source_question4_false : ¬ SourceQuestion4 := by
  intro h
  exact source_question4_counterexample (h 4 2 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))

end PottsBP
