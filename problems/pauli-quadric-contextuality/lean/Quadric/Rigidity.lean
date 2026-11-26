import Quadric.Four

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators

def ray (u : Word 4 → ℝ) : Mat 4 := fun i j => u i * u j

theorem optimal_spectrum {s : Assignment 4} (ho : (bad s).card = degree 4) :
    ∃ k : Word 4, (operator_hermitian s).eigenvalues k = 45 ∧
      ∀ i, i ≠ k → (operator_hermitian s).eigenvalues i = -3 := by
  classical
  let H := operator_hermitian s
  let v := H.eigenvalues
  have h1 : ∑ i, v i = 0 := by
    simpa [v] using (trace_power H 1).symm.trans (by simpa using trace_one s)
  have h2 : ∑ i, v i ^ 2 = 2160 := by
    rw [← trace_power H,trace_two,points_card]; norm_num [dim]
  have h3 : ∑ i, v i ^ 3 = 90720 := by
    rw [← trace_power H,trace_three,ho,degree_four,lines_card]; norm_num [dim]
  have cap (i) : v i ≤ 45 := by
    apply (show (16-1)*(3:ℝ)=45 by norm_num) ▸
      eigenvalue_cap v 16 3 (by norm_num [Fintype.card_pi]) (by norm_num)
        (by norm_num) h1 (by linarith only [h2]) i
  have nonneg (i) : 0 ≤ (45-v i)*(v i+3)^2 :=
    mul_nonneg (sub_nonneg.mpr (cap i)) (sq_nonneg _)
  have sl : ∑ i, (45-v i)*(v i+3)^2 = 0 := by
    have ex (i) : (45-v i)*(v i+3)^2 = 39*v i^2+261*v i+405-v i^3 := by ring
    simp_rw [ex,sum_sub_distrib,sum_add_distrib,← mul_sum,h1,h2,h3]
    norm_num [Fintype.card_pi]
  have roots (i) : v i=45 ∨ v i= -3 := by
    have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => nonneg j)).mp sl i (mem_univ _)
    rcases mul_eq_zero.mp hh with hh|hh
    · left; linarith
    · right; have := sq_eq_zero_iff.mp hh; linarith
  let top := (univ : Finset (Word 4)).filter fun i => v i=45
  have term' (i) : v i = 48*(if v i=45 then 1 else 0)-3 := by
    rcases roots i with hh|hh <;> rw [hh] <;> norm_num
  have hc : top.card=1 := by
    have hz : (∑ i, (48*(if v i=45 then (1:ℝ) else 0)-3)) = 0 :=
      (sum_congr rfl fun i _ => (term' i).symm).trans h1
    simp only [sum_sub_distrib,← mul_sum,sum_boole,sum_const,nsmul_eq_mul,
      card_univ] at hz
    change 48*(top.card : ℝ)-(Fintype.card (Word 4) : ℝ)*3=0 at hz
    norm_num [Fintype.card_pi] at hz
    exact_mod_cast (by linarith : (top.card : ℝ)=1)
  obtain ⟨k,hk⟩ := card_eq_one.mp hc
  have iff' (i) : v i=45 ↔ i=k := by
    simpa [top] using (show i ∈ top ↔ i=k by rw [hk]; simp)
  refine ⟨k,(iff' k).mpr rfl,fun i hi => ?_⟩
  exact (roots i).resolve_left (mt (iff' i).mp hi)

theorem optimal_projector {s : Assignment 4} (ho : (bad s).card = degree 4) :
    ∃ u : Word 4 → ℝ, (∑ i, u i^2)=1 ∧
      operator s = (48:ℝ) • ray u - (3:ℝ) • (1 : Mat 4) := by
  classical
  let H := operator_hermitian s
  let U := (H.eigenvectorUnitary : Mat 4)
  have hu : star U * U = 1 := unitary.coe_star_mul_self _
  have hv : U * star U = 1 := unitary.coe_mul_star_self _
  obtain ⟨k, hk, he⟩ := optimal_spectrum ho
  let u := fun i => U i k
  let E : Mat 4 := diagonal (fun i => if i=k then (1:ℝ) else 0)
  have diagval : diagonal H.eigenvalues = (48:ℝ) • E - (3:ℝ) • (1 : Mat 4) := by
    ext i j
    by_cases hij : i=j
    · subst j; by_cases hh : i=k
      · subst i; simp [H,E,Matrix.one_apply,hk]; norm_num
      · simp [H,E,Matrix.one_apply,hh,he i hh]
    · simp [E,Matrix.one_apply,diagonal_apply,hij]
  have outercol : U * E * star U = ray u := by
    ext i j
    simp only [E,mul_diagonal,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.star_apply,
      Matrix.conjTranspose_apply,star_trivial,ray,u]
    simp [mul_ite,ite_mul]
  refine ⟨u,?_,?_⟩
  · have hz := congrFun (congrFun hu k) k
    simpa [u,sq,mul_apply,Matrix.star_apply,Matrix.conjTranspose_apply] using hz
  · calc
      operator s = U * diagonal H.eigenvalues * star U := by
        simpa [U,Function.comp_def] using H.spectral_theorem
      _ = _ := by rw [diagval,mul_sub,sub_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,
                         Matrix.smul_mul,mul_one,outercol,hv]

theorem coefficient {s : Assignment 4} {p : Label 4} (hp : p ∈ points 4) :
    ((operator s)*pauli p).trace = 16*value (s p) := by
  simp only [operator,sum_mul,term,Matrix.smul_mul,trace_sum,trace_smul,smul_eq_mul]
  calc
    _ = ∑ x ∈ points 4, value (s x) * (if p=x then dim 4 else 0) :=
      sum_congr rfl fun _ hx => by rw [trace_pair hx]
    _ = _ := by simp [mul_ite,hp,dim,mul_comm]; norm_num

theorem optimal_flat_state {s : Assignment 4} (ho : (bad s).card=degree 4) :
    ∃ u : Word 4 → ℝ, (∑ i, u i^2)=1 ∧ ∀ p ∈ points 4,
      (ray u * pauli p).trace = value (s p)/3 := by
  obtain ⟨u,hn,hA⟩ := optimal_projector ho
  refine ⟨u,hn,fun p hp => ?_⟩
  have hc := coefficient (s:=s) hp
  rw [hA,sub_mul,Matrix.smul_mul,Matrix.smul_mul,one_mul,trace_sub,trace_smul,trace_smul,
    pauli_trace,if_neg (mem_points.mp hp).1] at hc
  simp only [smul_eq_mul,mul_zero,sub_zero] at hc
  linarith

end Quadric.Four
