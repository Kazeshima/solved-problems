import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Quadric
open Finset Matrix
open scoped BigOperators

theorem trace_power {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (h : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (h.eigenvalues i)^k := by
  let U := (h.eigenvectorUnitary : Matrix I I ℝ)
  let D := diagonal h.eigenvalues
  have hu : star U * U = 1 := unitary.coe_star_mul_self _
  have hv : U * star U = 1 := unitary.coe_mul_star_self _
  have hd : A = U * D * star U := by simpa [U,D,Function.comp_def] using h.spectral_theorem
  have hk : ∀ j : ℕ, A^j = U * D^j * star U := by
    intro j; induction j with
    | zero => simpa [hv]
    | succ j ih =>
      rw [pow_succ, ih, hd, pow_succ]
      calc
        _ = U * D^j * (star U * U) * D * star U := by noncomm_ring
        _ = _ := by rw [hu, mul_one, mul_assoc U]
  rw [hk, trace_mul_comm, ← mul_assoc, hu, one_mul]
  simp [D, diagonal_pow, trace, Matrix.diag]

theorem eigenvalue_cap {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → ℝ) (d a : ℝ) (hc : (Fintype.card I : ℝ) = d)
    (hd : 1 < d) (ha : 0 ≤ a) (h1 : ∑ i, v i = 0)
    (h2 : ∑ i, v i ^ 2 = d*(d-1)*a^2) :
    ∀ i, v i ≤ (d-1)*a := by
  classical
  intro i
  let t := (univ : Finset I).erase i
  have hi : i ∈ (univ : Finset I) := mem_univ _
  have ht : (t.card : ℝ) = d-1 := by
    have h := card_erase_add_one hi
    have hh : (t.card : ℝ)+1 = (Fintype.card I : ℝ) := by exact_mod_cast h
    linarith
  have hsum : ∑ j ∈ t, v j = -v i := by
    linarith only [sum_erase_add (s:=univ) v hi, h1]
  have hsq : ∑ j ∈ t, v j ^ 2 = d*(d-1)*a^2-v i^2 := by
    linarith only [sum_erase_add (s:=univ) (fun j => v j ^ 2) hi, h2]
  have hcs := sum_mul_sq_le_sq_mul_sq t (fun _ => (1:ℝ)) v
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, ht, hsum, hsq] at hcs
  have hscaled : d * (v i ^ 2) ≤ d * (((d-1)*a)^2) := by nlinarith only [hcs]
  have hbound := (mul_le_mul_left (by linarith : 0 < d)).mp hscaled
  exact le_of_not_gt fun hbad => by
    have hnn : 0 ≤ (d-1)*a := mul_nonneg (by linarith) ha
    nlinarith only [hbound, mul_pos (sub_pos.mpr hbad) (by linarith : 0 < v i + (d-1)*a)]

/-- Okumura's sharp cubic moment inequality in the normalization used below. -/
theorem cubic_bound {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → ℝ) (d a : ℝ) (hc : (Fintype.card I : ℝ) = d)
    (hd : 1 < d) (ha : 0 ≤ a) (h1 : ∑ i, v i = 0)
    (h2 : ∑ i, v i ^ 2 = d*(d-1)*a^2) :
    ∑ i, v i ^ 3 ≤ d*(d-1)*(d-2)*a^3 := by
  classical
  have cap := eigenvalue_cap v d a hc hd ha h1 h2
  have hp : 0 ≤ ∑ i, ((d-1)*a-v i)*(v i+a)^2 :=
    sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (cap i)) (sq_nonneg _)
  have expand (i : I) : ((d-1)*a-v i)*(v i+a)^2 =
      (d-3)*a*(v i)^2 + (2*d-3)*a^2*v i + (d-1)*a^3 - v i^3 := by ring
  simp_rw [expand, sum_sub_distrib, sum_add_distrib, ← mul_sum, h2, h1, mul_zero,
    add_zero, sum_const, nsmul_eq_mul, card_univ, hc] at hp
  linarith only [hp, show (d-3)*a*(d*(d-1)*a^2)+d*((d-1)*a^3) =
    d*(d-1)*(d-2)*a^3 by ring]

end Quadric
