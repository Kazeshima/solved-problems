import Quadric.Clifford
import Quadric.Counts

namespace Quadric.Five
open Finset
open scoped BigOperators

def form {n} (c x : Label n) : Bit := q x + polar c x

theorem polar_comm {n} (p r : Label n) : polar p r = polar r p := add_comm _ _
theorem polar_add_right {n} (p r t : Label n) : polar p (r+t) = polar p r+polar p t := by
  simp only [polar,cross_add,add_cross]; abel
theorem polar_add_left {n} (p r t : Label n) : polar (p+r) t = polar p t+polar r t := by
  simp only [polar,cross_add,add_cross]; abel
@[simp] theorem polar_zero {n} (p : Label n) : polar p 0=0 := by simp [polar,cross]
@[simp] theorem zero_polar {n} (p : Label n) : polar 0 p=0 := by simp [polar,cross]
@[simp] theorem q_zero (n : ℕ) : q (0:Label n)=0 := by simp [q]
theorem form_add {n} (c p r : Label n) : form c (p+r)=form c p+form c r+polar p r := by
  simp only [form,q_add,polar_add_right]; abel

def factor {n} (c p x : Label n) := chi (polar p x + form c p)
def centres {n} (c : Label n) : Finset (Label n) := univ.filter fun x => form c x≠0
def coversPoint {n} (c x p : Label n) : Prop := polar p x = form c p
instance {n} (c x p : Label n) : Decidable (coversPoint c x p) := inferInstanceAs (Decidable (_=_))

theorem factor_sum {n} (c : Label n) {p : Label n} (hp : p≠0) : ∑ x, factor c p x=0 := by
  simp only [factor,chi_add,←sum_mul,polar_sum hp,zero_mul]

theorem weighted_factor {n} (c p : Label n) :
    (∑ x, factor c p x * chi (form c x))=chi (q c)*dim n := by
  have ht (x : Label n) : factor c p x * chi (form c x) =
      chi (q (x+(c+p))) * chi (q c) := by
    simp only [factor,form,←chi_add,q_add,polar_add_right,polar_comm x c,polar_comm x p]
    congr 1
    abel_nf
    simp [CharTwo.two_nsmul,CharTwo.two_eq_zero]
  simp_rw [ht,←sum_mul]
  rw [sum_shift (c+p) (fun x => chi (q x)),gauss,mul_comm]

theorem form_sum {n} (c : Label n) : ∑ x, chi (form c x)=chi (q c)*dim n := by
  simpa [factor,form] using weighted_factor c 0

theorem centres_card {n} (c : Label n) :
    2*((centres c).card : ℝ) = dim n^2 - chi (q c)*dim n := by
  classical
  have h (x : Label n) : 2*(if form c x ≠ 0 then (1:ℝ) else 0) = 1-chi (form c x) := by
    by_cases hx : form c x=0 <;> norm_num [hx,chi]
  rw [centres,←sum_boole,mul_sum]
  simp_rw [h,sum_sub_distrib,form_sum]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,label_card]

theorem factor_mul {n} (c : Label n) {p r : Label n} (hp : polar p r=0) (x) :
    factor c p x*factor c r x=factor c (p+r) x := by
  simp only [factor,←chi_add,polar_add_left,form_add,hp,add_zero]
  congr 1; abel

private theorem ind_factor {n} (c p x : Label n) :
    2*(if coversPoint c x p then (1:ℝ) else 0) = 1+factor c p x := by
  have h (b d : Bit) : 2*(if b=d then (1:ℝ) else 0)=1+chi (b+d) := by
    fin_cases b <;> fin_cases d <;> norm_num [chi] <;>
      rw [if_pos (by decide : (2:Bit)=0)] <;> norm_num
  exact h _ _

/-- Number of centres covering a commuting line. This also counts elliptic quadrics through
a full-space line when c=0. -/
theorem cover_card {n} (c p r : Label n) (hp : p≠0) (hr : r≠0)
    (ht : p+r≠0) (hpr : polar p r=0) :
    8*(((centres c).filter fun x => coversPoint c x p ∧ coversPoint c x r).card : ℝ) =
      dim n^2 - 4*chi (q c)*dim n := by
  classical
  let I (x : Label n) := if form c x≠0 ∧ coversPoint c x p ∧ coversPoint c x r then (1:ℝ) else 0
  have expr (x : Label n) : 8*I x =
      1 + factor c p x + factor c r x + factor c (p+r) x -
      (chi (form c x) + factor c p x * chi (form c x) + factor c r x * chi (form c x) +
        factor c (p+r) x * chi (form c x)) := by
    have h0 : 2*(if form c x≠0 then (1:ℝ) else 0) = 1-chi (form c x) := by
      by_cases h : form c x=0 <;> norm_num [h,chi]
    calc
      _ = (2*(if coversPoint c x p then 1 else 0))*(2*(if coversPoint c x r then 1 else 0))*
          (2*(if form c x≠0 then (1:ℝ) else 0)) := by
            by_cases a : coversPoint c x p <;> by_cases b : coversPoint c x r <;>
              by_cases h : form c x=0 <;> norm_num [I,h,a,b]
      _ = _ := by rw [ind_factor,ind_factor,h0,←factor_mul c hpr]; ring
  have eqsum : (((centres c).filter fun x => coversPoint c x p ∧ coversPoint c x r).card : ℝ) =
      ∑ x, I x := by simp [centres,I,sum_boole,filter_filter,and_assoc]
  rw [eqsum,mul_sum]
  simp_rw [expr,sum_sub_distrib,sum_add_distrib]
  rw [factor_sum c hp,factor_sum c hr,factor_sum c ht,form_sum,weighted_factor,weighted_factor,
    weighted_factor]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,label_card]; ring

/-- Finite double counting, applicable to the violated contexts of any assignment. -/
theorem cover_bound {A B : Type*} (cent : Finset A) (faults : Finset B)
    (inside : A → B → Prop) [DecidableRel inside] (k m : ℕ)
    (hc : ∀ l ∈ faults, (cent.filter fun a => inside a l).card=m)
    (hs : ∀ a ∈ cent, k≤(faults.filter (inside a)).card) :
    cent.card*k ≤ faults.card*m := by
  classical
  calc
    _ = ∑ _a ∈ cent, k := by simp
    _ ≤ ∑ a ∈ cent, (faults.filter (inside a)).card := sum_le_sum hs
    _ = ∑ a ∈ cent, ∑ l ∈ faults, (if inside a l then (1:ℕ) else 0) := by simp [sum_boole]
    _ = ∑ l ∈ faults, ∑ a ∈ cent, (if inside a l then (1:ℕ) else 0) := sum_comm
    _ = _ := by simp_rw [sum_boole]; simpa using sum_const_nat (s:=faults) hc

end Quadric.Five
