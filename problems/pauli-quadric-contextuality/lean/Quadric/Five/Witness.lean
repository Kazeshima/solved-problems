import Quadric.Five
import Quadric.States

namespace Quadric.Five
open Finset Matrix
open scoped BigOperators

def mixed {n : ℕ} : Assignment n := fun p => decide (p.1≠0 ∧ p.2≠0)

theorem perp_character {n} (a x : Word n) :
    2*(∑ b, singular (a,b)*chi (dot b x)) =
    (if x=0 then dim n else 0)+(if x=a then dim n else 0) := by
  have term' (b : Word n) : 2*(singular (a,b)*chi (dot b x)) =
      chi (dot x b) + chi (dot (a+x) b) := by
    rw [←mul_assoc,twice_singular,add_dot,chi_add]
    simp only [q,dot_comm b x]; ring
  rw [mul_sum]; simp_rw [term',sum_add_distrib,sum_character]
  simp only [Four.word_zero]; by_cases h : a=x <;> simp [h,Ne.symm]

theorem mixed_entry {n} (x y : Word n) :
    operator (mixed (n:=n)) x y =
      if x=y then (if y=0 then dim n else 0)-1
      else 2-((if y=0 then dim n else 0)+(if x=0 then dim n else 0))/2 := by
  classical
  simp only [operator,Matrix.sum_apply]
  rw [point_sum,Fintype.sum_prod_type]
  have e (a : Word n) : x=y+a ↔ a=x+y := by
    constructor
    · rintro rfl; simp [add_right_comm]
    · rintro rfl; simp [add_left_comm]
  have inner (a : Word n) : (∑ b, singular (a,b)*term mixed (a,b) x y) =
      if a=x+y then ∑ b, singular (a,b)*(value (mixed (a,b))*chi (dot b y)) else 0 := by
    by_cases h : a=x+y <;> simp [term,pauli,e,h,Matrix.smul_apply]
  simp_rw [inner]; rw [sum_ite_eq',if_pos (mem_univ _)]
  have hz : term (mixed (n:=n)) 0 x y = if x=y then 1 else 0 := by simp [term,pauli,mixed,value]
  rw [hz]
  by_cases he : x=y
  · subst x; simp only [word_self,if_pos rfl]
    simp only [singular,q,Prod.fst_zero,zero_dot,if_pos rfl,mixed,ne_eq,not_true_eq_false,
      false_and,decide_false,value,Bool.false_eq_true,if_false,one_mul]
    simpa [dot_comm _ y] using congrArg (fun z : ℝ => z-1) (sum_character y)
  · let a := x+y
    have ha : a≠0 := mt (Four.word_zero x y).mp he
    have hterm (b : Word n) : singular (a,b)*(value (mixed (a,b))*chi (dot b y)) =
        (if b=0 then 2 else 0) - singular (a,b)*chi (dot b y) := by
      by_cases hb : b=0
      · subst b; simp [mixed,value,singular,q,chi]; norm_num
      · simp [mixed,value,hb,ha]
    rw [if_neg he,if_neg he,sub_zero]
    change (∑ b, singular (a,b)*(value (mixed (a,b))*chi (dot b y)))=_
    simp_rw [hterm,sum_sub_distrib]
    rw [sum_ite_eq',if_pos (mem_univ _)]
    have h := perp_character a y
    have hy : y=a ↔ x=0 := by dsimp [a]; simp [eq_comm]
    simp only [hy] at h
    linarith

private def blockMat (a b c d : ℝ) : Mat 5 := fun x y =>
  if x=0 then (if y=0 then a else b) else (if y=0 then c else d)

private theorem sum_blocks (a b : ℝ) :
    (∑ x : Word 5, if x=0 then a else b) = a+31*b := by
  classical
  rw [←sum_erase_add (s:=univ) (fun x : Word 5 => if x=0 then a else b) (mem_univ 0)]
  rw [sum_congr rfl (fun x hx => if_neg (mem_erase.mp hx).1)]
  norm_num [Fintype.card_pi]; ring

private theorem block_mul (a b c d e f g h : ℝ) :
    blockMat a b c d * blockMat e f g h = blockMat
      (a*e+31*b*g) (a*f+31*b*h) (c*e+31*d*g) (c*f+31*d*h) := by
  ext i j
  have term' (k : Word 5) : blockMat a b c d i k * blockMat e f g h k j =
      if k=0 then (if i=0 then a else c)*(if j=0 then e else f)
      else (if i=0 then b else d)*(if j=0 then g else h) := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> by_cases hk : k=0 <;> simp [blockMat,hi,hj,hk]
  rw [Matrix.mul_apply,sum_congr rfl (fun k _ => term' k),sum_blocks]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [blockMat,hi,hj] <;> ring

private theorem block_trace (a b c d : ℝ) : (blockMat a b c d).trace=a+31*d := by
  have term' (x : Word 5) : blockMat a b c d x x = if x=0 then a else d := by
    by_cases hx : x=0 <;> simp [blockMat,hx]
  exact (sum_congr rfl (fun x _ => term' x)).trans (sum_blocks a d)

theorem mixed_matrix : operator (mixed (n:=5)) =
    blockMat 34 (-14) (-14) 2 - (3:ℝ) • (1:Mat 5) := by
  ext x y
  by_cases hx : x=0 <;> by_cases hy : y=0 <;> by_cases hxy : x=y <;>
    simp_all [mixed_entry,blockMat,Matrix.one_apply,dim] <;> norm_num

theorem witness_count : (bad (mixed (n:=5))).card=6975 := by
  have h := trace_three (mixed (n:=5))
  rw [mixed_matrix,pow_succ,pow_two] at h
  simp only [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,
    block_mul,trace_sub,trace_smul,smul_eq_mul,block_trace] at h
  norm_num [dim,lines_card,Fintype.card_pi] at h
  exact_mod_cast (by linarith : ((bad (mixed (n:=5))).card : ℝ)=6975)

theorem witness_upper : degree 5 ≤ 6975 := by simpa only [witness_count] using degree_le (mixed (n:=5))

/-- The literal six-digit suffix in the follow-up cannot be the degree. -/
theorem degree_ne_6975975 : degree 5 ≠ 6975975 := by have := witness_upper; omega

end Quadric.Five
