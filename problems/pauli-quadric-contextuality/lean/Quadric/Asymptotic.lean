import Quadric.Moments
import Quadric.Spectral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Quadric
open Finset Filter
open scoped BigOperators Topology

/-- Full sign assignments can be restricted to the quadric. Values elsewhere are ignored. -/
noncomputable def degree (n : ℕ) : ℕ :=
  (univ : Finset (Assignment n)).inf' univ_nonempty fun s => (bad s).card

theorem degree_attained (n : ℕ) : ∃ s : Assignment n, degree n = (bad s).card := by
  obtain ⟨s,_,h⟩ := exists_mem_eq_inf' (s:=(univ : Finset (Assignment n))) univ_nonempty
    (fun s => (bad s).card)
  exact ⟨s,h⟩

theorem degree_le {n} (s : Assignment n) : degree n ≤ (bad s).card :=
  inf'_le _ (mem_univ s)

theorem upper (n : ℕ) : 2*(degree n : ℝ) ≤ (lines n).card := by
  let s : Assignment n := fun _ => false
  let t : Assignment n := fun _ => true
  have neg : ∑ z ∈ pairs n, score t z = -(∑ z ∈ pairs n, score s z) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro ⟨x,y⟩ hz
    simp [score_eval t hz,score_eval s hz,s,t,value]
  rw [pair_score_sum, pair_score_sum] at neg
  have hs : (degree n : ℝ) ≤ (bad s).card := by exact_mod_cast degree_le s
  have ht : (degree n : ℝ) ≤ (bad t).card := by exact_mod_cast degree_le t
  linarith

theorem dim_ge_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ dim n :=
  calc (4:ℝ) = 2^(2:ℕ) := by norm_num
       _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn

theorem line_pos {n : ℕ} (hn : 2 ≤ n) : 0 < ((lines n).card : ℝ) := by
  have hd := dim_ge_four hn
  have h := line_count n
  have hpos : 0 < (dim n-1)*(dim n-2)*(dim n+2)*(dim n+4) := by
    have : 0 < dim n - 2 := by linarith
    have : 0 < dim n - 1 := by linarith
    positivity
  linarith

theorem assignment_lower {n : ℕ} (hn : 2 ≤ n) (s : Assignment n) :
    1/2 - Real.sqrt (2*(dim n+2))/(dim n+4) ≤ ((bad s).card : ℝ)/(lines n).card := by
  let d := dim n
  let a := Real.sqrt ((d+2)/2)
  have hd : 4 ≤ d := dim_ge_four hn
  have hd0 : 0 < d := by linarith
  have h4 : 0 < d+4 := by linarith
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = (d+2)/2 := Real.sq_sqrt (by linarith)
  have hsqrt : Real.sqrt (2*(d+2)) = 2*a :=
    (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr (by nlinarith only [ha2])
  have hm : ((points n).card : ℝ) = (d-1)*a^2 := by
    rw [ha2]; linarith only [point_count n]
  let H := operator_hermitian s
  have h1 : ∑ i, H.eigenvalues i = 0 := by
    simpa using (trace_power H 1).symm.trans (by simpa using trace_one s)
  have h2 : ∑ i, H.eigenvalues i^2 = d*(d-1)*a^2 := by
    rw [← trace_power H 2,trace_two,hm]; change d*((d-1)*a^2)=_; ring
  have h3 := cubic_bound H.eigenvalues d a (word_card n) (by linarith) ha h1 h2
  rw [← trace_power H 3,trace_three] at h3
  let L : ℝ := (lines n).card
  let N : ℝ := (bad s).card
  change 6*d*(L-2*N) ≤ d*(d-1)*(d-2)*a^3 at h3
  have hb : 6*(L-2*N) ≤ (d-1)*(d-2)*a^3 := by
    apply (mul_le_mul_left hd0).mp; linarith only [h3]
  have hl : 48*L = (d-1)*(d-2)*(d+2)*(d+4) := line_count n
  have hmul : (d-1)*(d-2)*a^3*(d+4) = 24*a*L := by
    linear_combination (d-1)*(d-2)*a*(d+4)*ha2 - (a/2)*hl
  have hgap := mul_le_mul_of_nonneg_right hb h4.le
  rw [hmul] at hgap
  have hL : 0 < L := line_pos hn
  change 1/2-Real.sqrt (2*(d+2))/(d+4) ≤ N/L
  rw [hsqrt, show (1:ℝ)/2-2*a/(d+4) = (d+4-4*a)/(2*(d+4)) by
    field_simp; ring, div_le_div_iff₀ (by positivity) hL]
  nlinarith only [hgap]

noncomputable def fraction (n : ℕ) : ℝ := (degree n : ℝ)/(lines n).card

theorem contextuality_bounds (n : ℕ) (hn : 2 ≤ n) :
    1/2 - Real.sqrt (2*(dim n+2))/(dim n+4) ≤ fraction n ∧ fraction n ≤ 1/2 := by
  obtain ⟨s,hs⟩ := degree_attained n
  constructor
  · simpa only [fraction,hs] using assignment_lower hn s
  · unfold fraction
    rw [div_le_iff₀ (line_pos hn)]
    linarith only [upper n]

theorem contextuality_limit : Tendsto fraction atTop (𝓝 (1/2 : ℝ)) := by
  have hd : Tendsto dim atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have he : Tendsto (fun n => Real.sqrt (2/dim n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0:ℝ)).comp (hd.const_div_atTop 2)
  have hlo : Tendsto (fun n => 1/2-Real.sqrt (2/dim n)) atTop (𝓝 (1/2:ℝ)) := by
    simpa using (tendsto_const_nhds (x:=(1/2:ℝ))).sub he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hb := (contextuality_bounds n hn).1
    have hd4 := dim_ge_four hn
    have hd0 : 0 < dim n := by linarith
    have h4 : 0 < dim n + 4 := by linarith
    have hsq : (Real.sqrt (2*(dim n+2)))^2 = 2*(dim n+2) := Real.sq_sqrt (by positivity)
    have hsmall : (Real.sqrt (2/dim n))^2 = 2/dim n := Real.sq_sqrt (by positivity)
    have hz : Real.sqrt (2*(dim n+2)) ≤ Real.sqrt (2/dim n)*(dim n+4) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [hsq,mul_pow,hsmall]
      rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
      nlinarith
    linarith only [hb,(div_le_iff₀ h4).mpr hz]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (contextuality_bounds n hn).2

end Quadric
