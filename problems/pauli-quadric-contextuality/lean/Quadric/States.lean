import Quadric.Flat
import Quadric.Conventions
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Quadric.Four
open Matrix Finset
open scoped BigOperators

abbrev W := Word 4
abbrev Lab := Label 4
abbrev Point := {p : Lab // p ∈ points 4}
abbrev Signing := Point → Bit

def spin (s : Signing) (p : Lab) : Bit := if h : p ∈ points 4 then s ⟨p,h⟩ else 0
def assign (s : Signing) (p : Lab) : Bool := decide (spin s p ≠ 0)
@[simp] theorem spin_point (s : Signing) (p : Point) : spin s p.val = s p := by simp [spin,p.property]
@[simp] theorem sign_value (s : Signing) (p : Lab) : value (assign s p) = chi (spin s p) := by
  by_cases h : spin s p = 0 <;> simp [assign,value,chi,h]
noncomputable def violations (s : Signing) := bad (assign s)
abbrev Opt := {s : Signing // (violations s).card = degree 4}
noncomputable instance : Fintype Opt := Fintype.ofFinite _
def matrixOf (s : Signing) : Mat 4 := operator (assign s)
theorem matrix_injective : Function.Injective matrixOf := by
  intro s t h
  funext p
  have ht : 16 * chi (s p) = 16 * chi (t p) := by
    have h2 := congrArg (fun A : Mat 4 => (A*pauli p.val).trace) h
    simpa only [matrixOf,coefficient p.property,sign_value,spin_point] using h2
  exact (chi_inj _ _).mp (by linarith)
theorem state_ray (s : Opt) : ∃ u : W → ℝ, (∑ x, u x^2)=1 ∧
    matrixOf s.val = (48:ℝ) • ray u - (3:ℝ) • (1:Mat 4) := optimal_projector s.property

noncomputable def weight (s : Signing) (x : W) : ℝ := (matrixOf s x x + 3)/2

theorem weight_of_ray {s : Signing} {u : W → ℝ}
    (hu : matrixOf s = (48:ℝ) • ray u - (3:ℝ) • (1:Mat 4)) (x : W) :
    weight s x = 24*u x^2 := by
  simp [weight,hu,ray,Matrix.one_apply]; ring

theorem weight_sum (s : Opt) : ∑ x, weight s.val x = 24 := by
  obtain ⟨u,hn,hm⟩ := state_ray s
  simp_rw [weight_of_ray hm]; rw [← mul_sum,hn,mul_one]

def walsh (f : W → ℝ) (a : W) : ℝ := ∑ x, f x * chi (dot x a)

theorem walsh_pairing (f g : W → ℝ) :
    ∑ x, walsh f x * g x = ∑ x, f x * walsh g x := by
  simp only [walsh,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [dot_comm i j]; ring

theorem walsh_twice (f : W → ℝ) (y : W) :
    walsh (walsh f) y = 16*f y := by
  simp only [walsh,sum_mul]
  rw [sum_comm]
  have inner (x : W) : (∑ a, f x * chi (dot x a) * chi (dot a y)) =
      f x * (if x=y then 16 else 0) := by
    simp_rw [dot_comm _ y,mul_assoc,←chi_add,←add_dot,←mul_sum]
    rw [sum_character]; norm_num [word_zero,dim]
  simp_rw [inner]; simp [mul_ite,mul_comm]

theorem parseval (f : W → ℝ) :
    ∑ x, walsh f x ^ 2 = 16 * ∑ x, f x^2 := by
  simp only [sq]
  rw [walsh_pairing]
  simp_rw [walsh_twice]
  rw [mul_sum]; apply sum_congr rfl; intro i _; ring

theorem pure_diagonal {n} (s : Assignment n) (x : Word n) :
    operator s x x =
    ∑ b ∈ (univ : Finset (Word n)).erase 0, value (s (0,b)) * chi (dot b x) := by
  classical
  simp only [operator,Matrix.sum_apply]
  rw [point_sum, Fintype.sum_prod_type]
  have h (a : Word n) : (∑ b : Word n, singular (a,b) * term s (a,b) x x) =
      if a=0 then ∑ b, value (s (0,b))*chi (dot b x) else 0 := by
    by_cases ha : a=0 <;> simp [ha,term,pauli,singular,q]
  simp_rw [h]
  simp only [sum_ite_eq',mem_univ,if_true]
  rw [sum_erase_eq_sub (mem_univ (0:Word n))]
  simp [term,pauli]

def diagonalCoeffs (s : Signing) (x : W) : ℝ := if x=0 then 3 else value (assign s (0,x))
theorem twice_weight (s : Signing) (x : W) : 2*weight s x = walsh (diagonalCoeffs s) x := by
  rw [weight,matrixOf,pure_diagonal,walsh]
  rw [← sum_erase_add (s:=univ) (fun b => diagonalCoeffs s b * chi (dot b x)) (mem_univ 0)]
  have h (b : W) (hb : b ∈ (univ : Finset W).erase 0) :
    diagonalCoeffs s b = value (assign s (0,b)) := if_neg (mem_erase.mp hb).1
  simp only [diagonalCoeffs,ite_mul,if_pos rfl,zero_dot,chi_zero,mul_one]
  rw [show (∑ b ∈ (univ : Finset W).erase 0, if b = 0 then 3 * chi (dot b x)
    else value (assign s (0,b)) * chi (dot b x)) = _ from
      sum_congr rfl fun b hb => if_neg (mem_erase.mp hb).1]
  simp only [if_true]; ring

theorem weight_squares (s : Signing) : ∑ x, weight s x ^ 2 = 96 := by
  have h := parseval (diagonalCoeffs s)
  have hcoeff : ∑ x, diagonalCoeffs s x ^ 2 = 24 := by
    rw [← sum_erase_add (s:=univ) (fun x => diagonalCoeffs s x ^ 2)
      (mem_univ 0)]
    have ht (x) (hx : x ∈ (univ : Finset W).erase 0) :
        diagonalCoeffs s x ^ 2 = 1 := by
      simp only [diagonalCoeffs,if_neg (mem_erase.mp hx).1,sq,value_sq]
    rw [sum_congr rfl ht]
    norm_num [diagonalCoeffs,Fintype.card_pi]
  rw [hcoeff] at h
  simp_rw [← twice_weight,mul_pow,← mul_sum] at h
  linarith

theorem weight_level (s : Opt) (x : W) :
    ∃ k : Fin 10, weight s.val x = (k.val : ℝ) := by
  classical
  let t := (univ : Finset W).erase 0
  let neg (b : W) := value (assign s.val (0,b)) * chi (dot b x) = -1
  let N := (t.filter neg).card
  have ht : t.card=15 := by norm_num [t,Fintype.card_pi]
  have hterm (b : W) : value (assign s.val (0,b))*chi (dot b x) =
      1-2*(if neg b then (1:ℝ) else 0) := by
    unfold neg
    cases h : assign s.val (0,b) <;> by_cases hb : dot b x=0 <;> norm_num [h,hb,value,chi]
  have he : weight s.val x = 9-N := by
    rw [weight,matrixOf,pure_diagonal]
    change ((∑ b ∈ t, _) + 3)/2 = 9-(N:ℝ)
    simp_rw [hterm,sum_sub_distrib,←mul_sum,sum_boole]
    simp [N,ht]; ring
  obtain ⟨u,_,hu⟩ := state_ray s
  have hpos : 0 ≤ weight s.val x := by rw [weight_of_ray hu]; positivity
  have hN : N ≤ 9 := by exact_mod_cast (by linarith : (N:ℝ) ≤ 9)
  exact ⟨⟨9-N,by omega⟩,by rw [he,Nat.cast_sub hN]; norm_num⟩

noncomputable def level (s : Opt) (x : W) := (weight_level s x).choose
theorem level_spec (s : Opt) (x : W) : weight s.val x = ((level s x).val : ℝ) :=
  (weight_level s x).choose_spec

end Quadric.Four
