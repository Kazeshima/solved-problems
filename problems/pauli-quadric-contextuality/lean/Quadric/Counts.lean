import Quadric.Pauli

namespace Quadric
open Finset
open scoped BigOperators

/-- An ordered choice of two points on a context. -/
def pairs (n : ℕ) : Finset (Label n × Label n) :=
  ((points n) ×ˢ (points n)).filter fun z => z.1 + z.2 ∈ points n

def triple {n} (z : Label n × Label n) : Finset (Label n) := {z.1, z.2, z.1+z.2}
def lines (n : ℕ) := (pairs n).image triple

@[simp] theorem mem_pairs {n} {p r : Label n} : (p,r) ∈ pairs n ↔
    p ∈ points n ∧ r ∈ points n ∧ p+r ∈ points n := by
  simp only [pairs, mem_filter, mem_product]; tauto

@[simp] theorem twice_add {n} (p r : Label n) : p + (p+r) = r := by
  rw [← add_assoc, label_self, zero_add]
@[simp] theorem add_twice {n} (p r : Label n) : p+r+r = p := by
  rw [add_assoc, label_self, add_zero]

theorem add_eq_zero_iff_same {n} (p r : Label n) : p+r=0 ↔ p=r := by
  constructor
  · intro h; simpa [h] using (twice_add p r)
  · rintro rfl; exact label_self _

theorem pair_distinct {n} {p r : Label n} (h : (p,r) ∈ pairs n) :
    p ≠ r ∧ p ≠ p+r ∧ r ≠ p+r := by
  obtain ⟨⟨hp,_⟩,⟨hr,_⟩,⟨ht,_⟩⟩ := (by simpa only [mem_pairs,mem_points] using h :
    (p ≠ 0 ∧ q p = 0) ∧ (r ≠ 0 ∧ q r = 0) ∧ (p+r ≠ 0 ∧ q (p+r) = 0))
  exact ⟨mt (add_eq_zero_iff_same p r).mpr ht, fun he => hr (by simpa using he.symm),
    fun he => hp (by simpa using he.symm)⟩

/-- The quadratic character has Gauss sum 2^n, including the zero label. -/
theorem gauss (n : ℕ) : ∑ p : Label n, chi (q p) = dim n := by
  rw [Fintype.sum_prod_type]
  simp [q, sum_character]

theorem polar_sum {n} {p : Label n} (hp : p ≠ 0) :
    ∑ r : Label n, chi (polar p r) = 0 := by
  rcases p with ⟨a,b⟩
  rw [Fintype.sum_prod_type]
  simp only [polar, cross, chi_add]
  simp_rw [dot_comm _ a, ← mul_sum, sum_character, ← sum_mul, sum_character]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp_all

def singular {n} (p : Label n) : ℝ := if q p = 0 then 1 else 0

theorem twice_singular {n} (p : Label n) : 2 * singular p = 1 + chi (q p) := by
  by_cases h : q p=0 <;> simp [singular, chi, h] <;> norm_num

theorem singular_sum (n : ℕ) :
    2 * (∑ p : Label n, singular p) = dim n ^ 2 + dim n := by
  rw [mul_sum]; simp_rw [twice_singular]
  simp [sum_add_distrib, gauss, dim, sq]

theorem point_sum {n} (f : Label n → ℝ) :
    ∑ p ∈ points n, f p = (∑ p, singular p * f p) - f 0 := by
  classical
  have hz : q (0 : Label n) = 0 := by simp [q]
  rw [points, sum_filter]
  have h (p : Label n) :
      (if p ≠ 0 ∧ q p = 0 then f p else 0) =
        singular p * f p - (if p = 0 then f 0 else 0) := by
    by_cases hp : p=0 <;> by_cases hq : q p=0 <;> simp_all [singular]
  simp_rw [h]; simp [sum_sub_distrib]

theorem point_count (n : ℕ) :
    2 * ((points n).card : ℝ) = (dim n - 1) * (dim n + 2) := by
  have h := point_sum (n:=n) (fun _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  linarith only [h, singular_sum n, show (dim n-1)*(dim n+2) = dim n^2+dim n-2 by ring]

theorem singular_intersection {n} {p : Label n} (hp : p ∈ points n) :
    4 * (∑ r, singular r * singular (r+p)) = dim n ^ 2 + 2 * dim n := by
  obtain ⟨hp0,hq⟩ := mem_points.mp hp
  have term (r : Label n) : 4 * (singular r * singular (r+p)) =
      1 + chi (q r) + chi (q (r+p)) + chi (polar p r) := by
    have hc : chi (q r) * chi (q (r+p)) = chi (polar p r) := by
      rw [← chi_add, q_add, hq, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      simp [polar, add_comm]
    calc
      _ = (2 * singular r) * (2 * singular (r+p)) := by ring
      _ = _ := by rw [twice_singular, twice_singular]; nlinarith only [hc]
  rw [mul_sum]; simp_rw [term, sum_add_distrib]
  rw [sum_shift p (fun x => chi (q x)), gauss, polar_sum hp0]
  simp [dim]; ring

theorem neighbor_count {n} {p : Label n} (hp : p ∈ points n) :
    4 * (∑ r ∈ points n, (if p+r ∈ points n then (1:ℝ) else 0)) =
      (dim n-2)*(dim n+4) := by
  have hn := mem_points.mp hp
  have hz : q (0 : Label n) = 0 := by simp [q]
  have hterm (r : Label n) : singular r * (if p+r ∈ points n then (1:ℝ) else 0) =
      singular r * singular (r+p) - (if r=p then 1 else 0) := by
    by_cases he : r=p
    · subst r; simp [CharTwo.add_self_eq_zero, singular, hn, hz]
    · have hpr : p+r ≠ 0 := mt (add_eq_zero_iff_same p r).mp (Ne.symm he)
      have hrp : r+p ≠ 0 := by rwa [add_comm]
      by_cases h : q (r+p)=0 <;> simp [mem_points, hrp, singular, add_comm p r, h, he]
  rw [point_sum]; simp_rw [hterm]
  simp only [sum_sub_distrib, sum_ite_eq', mem_univ, if_true, add_zero, hp] 
  nlinarith only [singular_intersection hp]

theorem pair_count (n : ℕ) : 4 * ((pairs n).card : ℝ) =
    ((points n).card : ℝ) * ((dim n-2)*(dim n+4)) := by
  classical
  have card_as_sum : ((pairs n).card : ℝ) = ∑ p ∈ points n, ∑ r ∈ points n,
      (if p+r ∈ points n then (1:ℝ) else 0) := by
    rw [← sum_product']
    simp only [pairs, sum_boole]
  rw [card_as_sum, mul_sum]
  calc
    _ = ∑ _p ∈ points n, (dim n-2)*(dim n+4) := sum_congr rfl fun _ hp => neighbor_count hp
    _ = _ := by simp

end Quadric
