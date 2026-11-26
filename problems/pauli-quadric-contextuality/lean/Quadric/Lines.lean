import Quadric.Counts
import Mathlib.Tactic.LinearCombination

namespace Quadric
open Finset
open scoped BigOperators

theorem cross_self {n} (p : Label n) : cross p p = q p := dot_comm _ _
theorem cross_add {n} (p r t : Label n) : cross p (r+t) = cross p r + cross p t := dot_add .. 
theorem add_cross {n} (p r t : Label n) : cross (p+r) t = cross p t + cross r t := add_dot ..

theorem pair_cross {n} {p r : Label n} (hp : (p,r) ∈ pairs n) : cross r p = cross p r := by
  obtain ⟨hp,hr,ht⟩ := mem_pairs.mp hp
  have h := (mem_points.mp ht).2
  rw [q_add, (mem_points.mp hp).2, (mem_points.mp hr).2, zero_add, zero_add, polar] at h
  have := congrArg (fun b : Bit => cross p r + b) h
  simpa [← add_assoc, CharTwo.add_self_eq_zero] using this

/-- All six orderings have the same context and the same Pauli multiplication sign. -/
theorem reorder {n} {p r x y : Label n} (h : (p,r) ∈ pairs n)
    (hx : x ∈ triple (p,r)) (hy : y ∈ triple (p,r)) (hne : x ≠ y) :
    (x,y) ∈ pairs n ∧ triple (x,y) = triple (p,r) ∧ cross x y = cross p r := by
  obtain ⟨hp,hr,ht⟩ := mem_pairs.mp h
  have hpq := (mem_points.mp hp).2
  have hrq := (mem_points.mp hr).2
  have hc := pair_cross h
  have htp : p+r+p=r := by rw [add_comm (p+r), twice_add]
  have hrt : r+(p+r)=p := by rw [add_comm r, add_twice]
  simp only [triple, mem_insert, mem_singleton] at hx hy
  have hrp : r+p=p+r := add_comm _ _
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy <;> subst x <;> subst y <;>
    simp_all only [ne_eq, not_true_eq_false, mem_pairs, triple, twice_add, add_twice,
      htp, hrt, hrp, hp, hr, ht, and_self, cross_add, add_cross, cross_self,
      hpq, hrq, zero_add, add_zero, hc, eq_self_iff_true, true_and, and_true] <;>
    ext k <;> simp [or_assoc, or_left_comm, or_comm]

theorem triple_card {n} {p r : Label n} (hp : (p,r) ∈ pairs n) : (triple (p,r)).card = 3 := by
  obtain ⟨h1,h2,h3⟩ := pair_distinct hp
  simp [triple,h1,h2,h3]

theorem line_fiber {n} {l : Finset (Label n)} (hl : l ∈ lines n) :
    ((pairs n).filter fun z => triple z = l).card = 6 := by
  obtain ⟨⟨p,r⟩,hp,rfl⟩ := mem_image.mp hl
  have hf : ((pairs n).filter fun z => triple z = triple (p,r)) = (triple (p,r)).offDiag := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_offDiag]
    constructor
    · rintro ⟨hh, he⟩
      rw [← he]; exact ⟨by simp [triple], by simp [triple], (pair_distinct hh).1⟩
    · rintro ⟨hx,hy,hxy⟩
      have hh := reorder hp hx hy hxy
      exact ⟨hh.1,hh.2.1⟩
  rw [hf, offDiag_card, triple_card hp]

theorem six_to_one (n : ℕ) : (pairs n).card = (lines n).card * 6 := by
  rw [card_eq_sum_card_fiberwise (t:=lines n) (f:=triple) (fun _ => mem_image_of_mem _)]
  exact sum_const_nat fun _ hl => line_fiber hl

theorem line_count (n : ℕ) : 48 * ((lines n).card : ℝ) =
    (dim n-1)*(dim n-2)*(dim n+2)*(dim n+4) := by
  have h := pair_count n
  rw [six_to_one, Nat.cast_mul] at h
  norm_num at h
  linear_combination 2 * h + ((dim n-2)*(dim n+4)) * point_count n

abbrev Assignment (n : ℕ) := Label n → Bool
def value (b : Bool) : ℝ := if b then -1 else 1
@[simp] theorem value_sq (b : Bool) : value b * value b = 1 := by cases b <;> norm_num [value]

def score {n} (s : Assignment n) (z : Label n × Label n) : ℝ :=
  (∏ p ∈ triple z, value (s p)) * chi (cross z.1 z.2)

theorem score_eval {n} (s : Assignment n) {p r : Label n} (hp : (p,r) ∈ pairs n) :
    score s (p,r) = value (s p) * value (s r) * value (s (p+r)) * chi (cross p r) := by
  obtain ⟨h1,h2,h3⟩ := pair_distinct hp
  simp [score,triple,h1,h2,h3,mul_assoc]

theorem score_sign {n} (s : Assignment n) {p r : Label n} (hp : (p,r) ∈ pairs n) :
    score s (p,r) = 1 ∨ score s (p,r) = -1 := by
  rw [score_eval s hp]
  cases s p <;> cases s r <;> cases s (p+r) <;>
    by_cases hc : cross p r = 0 <;> norm_num [value,chi,hc]

noncomputable def representative {n} (l : Finset (Label n)) : Label n × Label n :=
  if h : ∃ z ∈ pairs n, triple z = l then h.choose else 0

theorem rep_spec {n} {l : Finset (Label n)} (hl : l ∈ lines n) :
    representative l ∈ pairs n ∧ triple (representative l) = l := by
  classical
  have hh := mem_image.mp hl
  simpa only [representative, dif_pos hh] using hh.choose_spec

theorem score_rep {n} (s : Assignment n) {p r : Label n} (hp : (p,r) ∈ pairs n) :
    score s (representative (triple (p,r))) = score s (p,r) := by
  have hs := rep_spec (mem_image_of_mem triple hp)
  generalize he : representative (triple (p,r)) = z at *
  rcases z with ⟨x,y⟩
  have hx : x ∈ triple (p,r) := hs.2 ▸ (by simp [triple] : x ∈ triple (x,y))
  have hy : y ∈ triple (p,r) := hs.2 ▸ (by simp [triple] : y ∈ triple (x,y))
  have hh := reorder hp hx hy (pair_distinct hs.1).1
  simp only [score,hs.2,hh.2.2]

noncomputable def bad {n} (s : Assignment n) : Finset (Finset (Label n)) :=
  (lines n).filter fun l => score s (representative l) = -1

theorem pair_score_sum {n} (s : Assignment n) :
    ∑ z ∈ pairs n, score s z = 6 * (((lines n).card : ℝ) - 2*(bad s).card) := by
  classical
  let f (l : Finset (Label n)) := score s (representative l)
  have hh : ∑ z ∈ pairs n, score s z = ∑ z ∈ pairs n, f (triple z) :=
    sum_congr rfl fun ⟨_,_⟩ hz => (score_rep s hz).symm
  rw [hh, ← sum_fiberwise_of_maps_to' (t:=lines n) (fun _ => mem_image_of_mem triple) f]
  have hterm (l) (hl : l ∈ lines n) :
      ∑ _z ∈ (pairs n).filter (fun z => triple z = l), f l =
        6 * (1 - 2 * (if f l = -1 then (1:ℝ) else 0)) := by
    simp only [sum_const, nsmul_eq_mul, line_fiber hl]
    have hr := (rep_spec hl).1
    have hv : f l = 1 ∨ f l = -1 := score_sign s (p:=(representative l).1) (r:=(representative l).2) hr
    rcases hv with hv|hv <;> simp [hv] <;> norm_num
  rw [sum_congr rfl hterm, ← mul_sum, sum_sub_distrib, ← mul_sum]
  simp [bad, f, sum_boole]

end Quadric
