import Quadric.Rigidity

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators

theorem flat_iff_optimal (s : Assignment 4) :
    (bad s).card = degree 4 ↔ ∃ u : Word 4 → ℝ, (∑ i, u i^2) = 1 ∧
    ∀ p ∈ points 4, (ray u * pauli p).trace = value (s p)/3 := by
  constructor
  · exact optimal_flat_state
  · rintro ⟨u, hn, hflat⟩
    let A := operator s
    let R := ray u
    let C : Mat 4 := (48:ℝ) • R - (3:ℝ) • (1:Mat 4)
    have hR : R*R=R := by
      ext x y
      simp only [R,Matrix.mul_apply,ray]
      calc
        _ = ∑ j, u x * (u j ^ 2) * u y := sum_congr rfl fun _ _ => by ring
        _ = _ := by rw [← sum_mul,← mul_sum,hn,mul_one]
    have trR : R.trace=1 := by simpa [R,ray,trace,Matrix.diag,sq] using hn
    have hCh : C.IsHermitian := by
      ext x y
      simp [C,R,ray,Matrix.one_apply,eq_comm,mul_comm,Matrix.conjTranspose_apply]
    have trA : A.trace=0 := trace_one s
    have trA2 : (A*A).trace=2160 := by
      convert trace_two s using 1 <;> norm_num [A,pow_two,dim,points_card]
    have trAR : (A*R).trace=45 := by
      simp only [A,operator,sum_mul,term,Matrix.smul_mul,trace_sum,trace_smul,smul_eq_mul]
      have hh (p) (hp : p ∈ points 4) : value (s p)*(pauli p * R).trace = 1/3 := by
        rw [trace_mul_comm,hflat p hp,mul_div_assoc',value_sq]
      rw [sum_congr rfl hh]; norm_num [points_card]
    have trAC : (A*C).trace=2160 := by
      simp only [C,mul_sub,Matrix.mul_smul,mul_one,trace_sub,trace_smul,smul_eq_mul,trAR,trA]
      norm_num
    have hc2 : C*C=(2016:ℝ) • R + (9:ℝ) • (1:Mat 4) := by
      simp only [C,sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,hR,one_mul,mul_one,
        smul_sub,smul_smul]
      ext i j; simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring
    have trC2 : (C*C).trace=2160 := by
      rw [hc2]; norm_num [trace_add,trace_smul,trR,Fintype.card_pi]
    have hAC : A=C := by
      apply sub_eq_zero.mp
      apply symmetric_zero ((operator_hermitian s).sub hCh)
      simp only [sub_mul,mul_sub,trace_sub]
      rw [trace_mul_comm C,trAC,trA2,trC2]; norm_num
    have h3 := trace_three s
    change (A^3).trace = _ at h3
    rw [hAC,pow_succ,pow_two,hc2] at h3
    simp only [C,add_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,hR,
      trace_add,trace_sub,trace_smul,smul_eq_mul,trR] at h3
    norm_num [dim,lines_card,Fintype.card_pi] at h3
    rw [degree_four]
    exact_mod_cast (by linarith : ((bad s).card : ℝ)=315)

end Quadric.Four
