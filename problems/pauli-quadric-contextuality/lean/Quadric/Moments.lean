import Quadric.Lines

namespace Quadric
open Finset Matrix
open scoped BigOperators

def term {n} (s : Assignment n) (p : Label n) : Mat n := value (s p) • pauli p
def operator {n} (s : Assignment n) : Mat n := ∑ p ∈ points n, term s p

theorem operator_hermitian {n} (s : Assignment n) : (operator s).IsHermitian := by
  unfold Matrix.IsHermitian operator
  rw [conjTranspose_sum]
  apply sum_congr rfl
  intro p hp
  simp only [term, conjTranspose_smul, star_trivial, (pauli_hermitian (mem_points.mp hp).2).eq]

theorem trace_one {n} (s : Assignment n) : (operator s).trace = 0 := by
  rw [operator, trace_sum]
  apply sum_eq_zero
  intro p hp
  simp [term, trace_smul, pauli_trace, (mem_points.mp hp).1]

theorem trace_pair {n} {p : Label n} (hp : p ∈ points n) (r : Label n) :
    (pauli p * pauli r).trace = if r=p then dim n else 0 := by
  simp only [pauli_mul, trace_smul, pauli_trace, add_eq_zero_iff_same, smul_eq_mul]
  by_cases he : r=p
  · subst r; simp [cross_self, (mem_points.mp hp).2]
  · simp [he, Ne.symm he]

theorem trace_triple {n} (p r : Label n) {t : Label n} (ht : t ∈ points n) :
    ((pauli p * pauli r) * pauli t).trace = if t=p+r then chi (cross p r)*dim n else 0 := by
  simp only [pauli_mul, Matrix.smul_mul, trace_smul, pauli_trace, add_eq_zero_iff_same, smul_eq_mul]
  by_cases he : t=p+r
  · rw [← he]; simp [cross_self, (mem_points.mp ht).2]
  · simp [he, Ne.symm he]

theorem trace_two {n} (s : Assignment n) :
    ((operator s)^2).trace = dim n * (points n).card := by
  simp only [pow_two,operator,sum_mul,mul_sum,trace_sum]
  have inner (p : Label n) (hp : p ∈ points n) :
      ∑ r ∈ points n, (term s p * term s r).trace = dim n := by
    simp only [term,Matrix.smul_mul,Matrix.mul_smul,trace_smul,smul_eq_mul,trace_pair hp,
      mul_ite,mul_zero,sum_ite_eq',hp,if_true,← mul_assoc,value_sq,one_mul]
  rw [sum_comm, sum_congr rfl inner]
  simp [mul_comm]

theorem trace_three {n} (s : Assignment n) :
    ((operator s)^3).trace = 6*dim n*(((lines n).card : ℝ)-2*(bad s).card) := by
  have expand : ((operator s)^3).trace = ∑ p ∈ points n, ∑ r ∈ points n, ∑ t ∈ points n,
      ((term s p * term s r) * term s t).trace := by
    simp only [pow_succ,pow_zero,one_mul,operator,sum_mul,mul_sum,trace_sum]
    calc
      _ = ∑ t ∈ points n, ∑ p ∈ points n, ∑ r ∈ points n,
          (term s p * term s r * term s t).trace := sum_congr rfl fun _ _ => sum_comm
      _ = ∑ p ∈ points n, ∑ t ∈ points n, ∑ r ∈ points n,
          (term s p * term s r * term s t).trace := sum_comm
      _ = _ := sum_congr rfl fun _ _ => sum_comm
  have inner (p r : Label n) (hp : p ∈ points n) (hr : r ∈ points n) :
      ∑ t ∈ points n, ((term s p * term s r) * term s t).trace =
        if p+r ∈ points n then dim n * score s (p,r) else 0 := by
    have hh (t : Label n) (ht : t ∈ points n) :
        ((term s p * term s r) * term s t).trace = if t=p+r then
          value (s p)*value (s r)*value (s t)*chi (cross p r)*dim n else 0 := by
      simp only [term,Matrix.smul_mul,Matrix.mul_smul,trace_smul,smul_eq_mul,trace_triple p r ht]
      split_ifs <;> ring
    rw [sum_congr rfl hh, sum_ite_eq']
    split_ifs with h
    · rw [score_eval s (mem_pairs.mpr ⟨hp,hr,h⟩)]; ring
    · rfl
  have ordered : ((operator s)^3).trace = dim n * ∑ z ∈ pairs n, score s z := by
    rw [expand,mul_sum,pairs,sum_filter,sum_product]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    exact inner p r hp hr
  rw [ordered, pair_score_sum]; ring

end Quadric
