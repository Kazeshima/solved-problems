import Quadric.Asymptotic

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators

theorem points_card : (points 4).card = 135 := by
  have h := point_count 4
  norm_num [dim] at h
  exact_mod_cast (by linarith : ((points 4).card : ℝ) = 135)

theorem lines_card : (lines 4).card = 1575 := by
  have h := line_count 4
  norm_num [dim] at h
  exact_mod_cast (by linarith : ((lines 4).card : ℝ) = 1575)

def mixed : Assignment 4 := fun p => decide (p.1 ≠ 0 ∧ p.2 ≠ 0)
def v (x : Word 4) : ℝ := if x=0 then 3 else -1
def outer : Mat 4 := fun x y => v x * v y
def candidate : Mat 4 := (2:ℝ) • outer - (3:ℝ) • (1 : Mat 4)

theorem norm_v : ∑ x, v x * v x = 24 := by
  have h (x : Word 4) : v x * v x = 1 + (if x=0 then 8 else 0) := by
    by_cases hh : x=0 <;> norm_num [v,hh]
  simp_rw [h, sum_add_distrib]
  norm_num [Fintype.card_pi]

theorem outer_square : outer * outer = (24:ℝ) • outer := by
  ext x y
  simp only [Matrix.mul_apply,outer,Matrix.smul_apply,smul_eq_mul]
  calc
    _ = ∑ j, v x * (v j * v j) * v y := sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [← sum_mul, ← mul_sum, norm_v]; ring

theorem outer_trace : outer.trace = 24 := norm_v

theorem word_zero {n} (x y : Word n) : x+y=0 ↔ x=y := by
  constructor
  · intro h
    have := congrArg (fun z : Word n => x+z) h
    simpa [← add_assoc] using this.symm
  · rintro rfl; simp

theorem flat_expectation {p : Label 4} (hp : p ∈ points 4) :
    (outer * pauli p).trace = 8 * value (mixed p) := by
  obtain ⟨hp0,hq⟩ := mem_points.mp hp
  rcases p with ⟨a,b⟩
  have hab : dot b a = 0 := (dot_comm _ _).trans hq
  have hh (x : Word 4) : v x * v (x+a) * chi (dot b x) =
      chi (dot b x) + (if x=0 then (if a=0 then 16 else 0)-4 else 0)
        - (if x=a then 4 else 0) := by
    by_cases h1 : x=0
    · subst x; by_cases h2 : a=0 <;> norm_num [v,h2,eq_comm]
    · by_cases h2 : x=a
      · subst x; simp [v,h1,hab]; ring
      · simp [v,h1,h2,word_zero]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,outer,pauli,mul_ite,mul_zero,
    sum_ite_eq', mem_univ, if_true]
  simp_rw [hh,sum_sub_distrib,sum_add_distrib]
  rw [sum_character]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    simp_all [dim,mixed,value,Prod.ext_iff] <;> norm_num

theorem operator_outer : ((operator mixed)*outer).trace = 1080 := by
  simp only [operator,sum_mul,term,Matrix.smul_mul,trace_sum,trace_smul,smul_eq_mul]
  have hx (p : Label 4) (hp : p ∈ points 4) :
      value (mixed p) * (pauli p * outer).trace = 8 := by
    rw [trace_mul_comm, flat_expectation hp]
    calc
      _ = 8 * (value (mixed p)*value (mixed p)) := by ring
      _ = 8 := by simp
  rw [sum_congr rfl hx]
  norm_num [points_card]

theorem symmetric_zero {M : Mat 4} (hm : M.IsHermitian) (ht : (M*M).trace=0) : M=0 := by
  have symm (i j : Word 4) : M j i = M i j := by simpa using congrFun (congrFun hm.eq i) j
  have he : ∑ i, ∑ j, (M i j)^2 = 0 := by
    change (∑ i, ∑ j, M i j * M j i) = 0 at ht
    convert ht using 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [symm i j, sq]
  have nonneg (i : Word 4) : 0 ≤ ∑ j, (M i j)^2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  ext i j
  have hrow := (sum_eq_zero_iff_of_nonneg (fun i _ => nonneg i)).mp he i (mem_univ _)
  have hz := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (M i j))).mp hrow j (mem_univ _)
  simpa using hz

private theorem candidate_hermitian : candidate.IsHermitian := by
  ext i j
  simp [candidate,outer,Matrix.one_apply,eq_comm,mul_comm,Matrix.conjTranspose_apply]

private theorem candidate_square : candidate*candidate = (84:ℝ) • outer + (9:ℝ) • (1:Mat 4) := by
  simp only [candidate,sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,outer_square,
    one_mul,mul_one,smul_sub,smul_smul]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem witness_operator : operator mixed = candidate := by
  let A := operator mixed
  have hA : A.IsHermitian := operator_hermitian mixed
  have hA2 : (A*A).trace = 2160 := by
    convert trace_two mixed using 1 <;> norm_num [A,pow_two,dim,points_card]
  have hAC : (A*candidate).trace = 2160 := by
    simp only [candidate,mul_sub,Matrix.mul_smul,mul_one,trace_sub,trace_smul,
      smul_eq_mul,A,operator_outer,trace_one]
    norm_num
  have hC2 : (candidate*candidate).trace = 2160 := by
    rw [candidate_square]; norm_num [trace_add,trace_smul,outer_trace,Fintype.card_pi]
  apply sub_eq_zero.mp
  apply symmetric_zero (hA.sub candidate_hermitian)
  simp only [sub_mul,mul_sub,trace_sub]
  rw [trace_mul_comm candidate, hAC,hA2,hC2]; norm_num

theorem witness_count : (bad mixed).card = 315 := by
  have hh := trace_three mixed
  rw [witness_operator, pow_succ, pow_two, candidate_square] at hh
  simp only [candidate,add_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,
    outer_square,trace_add,trace_sub,trace_smul,smul_eq_mul,outer_trace] at hh
  norm_num [dim,lines_card,Fintype.card_pi] at hh
  exact_mod_cast (by linarith : ((bad mixed).card : ℝ) = 315)

theorem degree_four : degree 4 = 315 := by
  have hlo := (contextuality_bounds 4 (by decide)).1
  have hsqrt : Real.sqrt 36 = 6 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num [dim,fraction,lines_card,hsqrt] at hlo
  have hup := degree_le mixed
  rw [witness_count] at hup
  exact le_antisymm hup (by exact_mod_cast (by linarith : (315:ℝ) ≤ degree 4))

end Quadric.Four
