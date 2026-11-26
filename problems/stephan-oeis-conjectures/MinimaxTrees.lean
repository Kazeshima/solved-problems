import Mathlib

/-!
# Stephan's Conjecture 85: minimax trees and ordered partitions into odd blocks

OEIS A080795 counts minimax trees on `n` nodes (Foata and Han).  Its exponential generating
function `A` satisfies `A' = 2 A² - 1`, `A(0) = 1`, which is the recurrence recorded in the entry:

  `a(n+1) = 2 * Sum_{k=0..n} binomial(n,k) * a(k) * a(n-k) - 0^n`,   `a(0) = 1`.

OEIS A006154 counts ordered partitions of an `n`-set into blocks of odd size.  Its exponential
generating function is `1 / (1 - sinh x)`; choosing the first block gives

  `b(n+1) = Sum_{j odd} binomial(n+1, j) * b(n+1-j)`,   `b(0) = 1`.

Ralf Stephan conjectured in 2004 that `a(2n) = 2^n * b(2n)` (Conjecture 85 of "Prove or
disprove.  100 conjectures from the OEIS").  This file proves it for the two sequences defined
by these recurrences: `MinimaxTrees.a_even`.

The proof works with formal power series over `ℝ`.  Write `ω = √2`, `P = e^{ωx}`, `M = e^{-ωx}`.

* `A` solves the Riccati equation, and `A = -U'/(2U)` for `U = (1-ω) P + (1+ω) M`.  In the form
  `2 A U = V` with `V = -U'`, this follows from uniqueness for the linear equation `Q' = 2 A Q`.
* `B (1 - sinh x) = 1`; substituting `ω x` for `x` gives `B̃ (2 - P + M) = 2`.
* Adding each identity to its image under `x ↦ -x` and using `P M = 1`, `ω² = 2` gives
  `(A(x) + A(-x)) W = 16 = (B̃(x) + B̃(-x)) W` with `W = 2 (6 - P² - M²)`, a series with nonzero
  constant term.  Comparing coefficients of `x^(2n)` finishes the proof.
-/

open PowerSeries Finset
open scoped Nat

namespace MinimaxTrees

/-! ## The two sequences -/

/-- OEIS A080795 (minimax trees on `n` nodes), by the recurrence stated in the entry. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * (∑ k : Fin (n + 1), n.choose k * a k * a (n - k)) - 0 ^ n
decreasing_by
  · exact k.isLt
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- OEIS A006154 (ordered partitions of an `n`-set into blocks of odd size): the first block
has odd size `k + 1`, chosen in `binomial(n+1, k+1)` ways. -/
def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), if Even (k : ℕ) then (n + 1).choose (k + 1) * b (n - k) else 0
decreasing_by
  exact Nat.lt_succ_of_le (Nat.sub_le _ _)

theorem a_zero : a 0 = 1 := by rw [a]

theorem a_succ (n : ℕ) :
    a (n + 1) = 2 * (∑ k ∈ range (n + 1), n.choose k * a k * a (n - k)) - 0 ^ n := by
  rw [a, Fin.sum_univ_eq_sum_range (fun k => n.choose k * a k * a (n - k)) (n + 1)]

theorem b_zero : b 0 = 1 := by rw [b]

theorem b_succ (n : ℕ) :
    b (n + 1) = ∑ k ∈ range (n + 1),
      if Even k then (n + 1).choose (k + 1) * b (n - k) else 0 := by
  rw [b, Fin.sum_univ_eq_sum_range
    (fun k => if Even k then (n + 1).choose (k + 1) * b (n - k) else 0) (n + 1)]

/-- The first terms of `a` agree with OEIS A080795. -/
theorem a_values :
    a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 20 ∧ a 4 = 128 ∧ a 5 = 1024 ∧ a 6 = 9856 := by
  have h1 : a 1 = 1 := by
    have h := a_succ 0
    simpa [a_zero] using h
  have h2 : a 2 = 4 := by
    have h := a_succ 1
    simpa [sum_range_succ, a_zero, h1] using h
  have h3 : a 3 = 20 := by
    have h := a_succ 2
    simpa [sum_range_succ, a_zero, h1, h2, Nat.choose] using h
  have h4 : a 4 = 128 := by
    have h := a_succ 3
    simpa [sum_range_succ, a_zero, h1, h2, h3, Nat.choose] using h
  have h5 : a 5 = 1024 := by
    have h := a_succ 4
    simpa [sum_range_succ, a_zero, h1, h2, h3, h4, Nat.choose] using h
  have h6 : a 6 = 9856 := by
    have h := a_succ 5
    simpa [sum_range_succ, a_zero, h1, h2, h3, h4, h5, Nat.choose] using h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The first terms of `b` agree with OEIS A006154. -/
theorem b_values :
    b 1 = 1 ∧ b 2 = 2 ∧ b 3 = 7 ∧ b 4 = 32 ∧ b 5 = 181 ∧ b 6 = 1232 := by
  have h1 : b 1 = 1 := by
    have h := b_succ 0
    simpa [b_zero] using h
  have h2 : b 2 = 2 := by
    have h := b_succ 1
    simpa [sum_range_succ, b_zero, h1, Nat.choose] using h
  have h3 : b 3 = 7 := by
    have h := b_succ 2
    simpa [sum_range_succ, b_zero, h1, h2, Nat.choose, Nat.even_add_one] using h
  have h4 : b 4 = 32 := by
    have h := b_succ 3
    simpa [sum_range_succ, b_zero, h1, h2, h3, Nat.choose, Nat.even_add_one] using h
  have h5 : b 5 = 181 := by
    have h := b_succ 4
    simpa [sum_range_succ, b_zero, h1, h2, h3, h4, Nat.choose, Nat.even_add_one] using h
  have h6 : b 6 = 1232 := by
    have h := b_succ 5
    simpa [sum_range_succ, b_zero, h1, h2, h3, h4, h5, Nat.choose, Nat.even_add_one] using h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The recurrence for `a` over `ℝ`, without truncated subtraction. -/
theorem a_succ_cast (n : ℕ) : (a (n + 1) : ℝ) =
    2 * ∑ k ∈ range (n + 1), (n.choose k : ℝ) * a k * a (n - k) - (if n = 0 then 1 else 0) := by
  rw [a_succ]
  cases n with
  | zero => simp [a_zero]; norm_num
  | succ m => simp

/-! ## Generating functions -/

noncomputable section

/-- The exponential generating function of `a`. -/
def A : ℝ⟦X⟧ := mk fun n => (a n : ℝ) / n !

/-- The exponential generating function of `b`. -/
def B : ℝ⟦X⟧ := mk fun n => (b n : ℝ) / n !

/-- The series `e^{c x}`. -/
def E (c : ℝ) : ℝ⟦X⟧ := rescale c (exp ℝ)

theorem coeff_E (c : ℝ) (n : ℕ) : coeff ℝ n (E c) = c ^ n / n ! := by
  rw [E, coeff_rescale, coeff_exp]
  simp [div_eq_mul_inv]

theorem E_mul (c d : ℝ) : E c * E d = E (c + d) := exp_mul_exp_eq_exp_add c d

theorem E_zero : E 0 = 1 := by
  ext n
  rw [coeff_E, coeff_one]
  cases n <;> simp

theorem rescale_E (c d : ℝ) : rescale d (E c) = E (c * d) := rescale_rescale _ _ _

theorem rescale_C' (c r : ℝ) : rescale c (C ℝ r) = C ℝ r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

theorem derivative_E (c : ℝ) : d⁄dX ℝ (E c) = C ℝ c * E c := by
  ext n
  rw [coeff_derivative, coeff_C_mul, coeff_E, coeff_E, Nat.factorial_succ]
  have h1 : (n ! : ℝ) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Uniqueness for a homogeneous linear equation: `W' = G W`, `W(0) = 0` force `W = 0`. -/
theorem eq_zero_of_derivative_eq_mul {W G : ℝ⟦X⟧} (h : d⁄dX ℝ W = G * W)
    (h0 : constantCoeff ℝ W = 0) : W = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, h0]
    | succ m =>
      have h1 := congrArg (coeff ℝ m) h
      rw [coeff_derivative, coeff_mul] at h1
      have h2 : ∑ p ∈ antidiagonal m, coeff ℝ p.1 G * coeff ℝ p.2 W = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hp' : p.2 < m + 1 := Nat.lt_succ_of_le (antidiagonal.snd_le hp)
        rw [ih p.2 hp', mul_zero]
      rw [h2] at h1
      have h3 : ((m : ℝ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h1).resolve_right h3

/-- The Riccati equation `A' = 2 A² - 1`. -/
theorem derivative_A : d⁄dX ℝ A = 2 * (A * A) - 1 := by
  ext n
  rw [coeff_derivative, map_sub, show (2 : ℝ⟦X⟧) = C ℝ 2 from (map_ofNat (C ℝ) 2).symm,
    coeff_C_mul, coeff_mul, coeff_one, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [A, coeff_mk]
  have hn : (n ! : ℝ) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have key : ∀ k ∈ range (n + 1), (n.choose k : ℝ) * a k * a (n - k)
      = n ! * ((a k : ℝ) / k ! * ((a (n - k) : ℝ) / (n - k)!)) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have e1 : (k ! : ℝ) ≠ 0 := by positivity
    have e2 : ((n - k)! : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_choose ℝ hk']
    field_simp
    ring
  rw [a_succ_cast, Finset.sum_congr rfl key, ← Finset.mul_sum, Nat.factorial_succ]
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    simp only [hne, if_false, sub_zero]
    field_simp
    ring

theorem constantCoeff_A : constantCoeff ℝ A = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, A, coeff_mk, a_zero]
  simp

/-- `B = 1 + sinh · B`, written without division: `2 B = 2 + (e^x - e^{-x}) B`. -/
theorem two_mul_B : 2 * B = 2 + (E 1 - E (-1)) * B := by
  ext n
  rw [show (2 : ℝ⟦X⟧) = C ℝ 2 from (map_ofNat (C ℝ) 2).symm, map_add, coeff_C_mul, coeff_C,
    coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sub, coeff_E, B, coeff_mk, one_pow]
  cases n with
  | zero => simp [b_zero]
  | succ m =>
    rw [Finset.sum_range_succ', b_succ]
    have hm : ((m + 1)! : ℝ) ≠ 0 := by positivity
    simp only [Nat.succ_sub_succ, pow_zero, Nat.factorial_zero, Nat.cast_one, sub_self, zero_div,
      zero_mul, add_zero, Nat.succ_ne_zero, if_false, zero_add]
    rw [Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k + 1 ≤ m + 1 := Nat.succ_le_of_lt (mem_range.mp hk)
    have e1 : ((k + 1)! : ℝ) ≠ 0 := by positivity
    have e2 : ((m - k)! : ℝ) ≠ 0 := by positivity
    by_cases hev : Even k
    · rw [if_pos hev, Odd.neg_one_pow hev.add_one]
      push_cast
      rw [Nat.cast_choose ℝ hk', Nat.succ_sub_succ]
      field_simp
      ring
    · have hodd : Odd k := Nat.not_even_iff_odd.mp hev
      rw [if_neg hev, Even.neg_one_pow hodd.add_one]
      simp

/-! ## The main identity -/

/-- **Stephan's Conjecture 85.**  `A080795(2n) = 2^n * A006154(2n)`. -/
theorem a_even (n : ℕ) : a (2 * n) = 2 ^ n * b (2 * n) := by
  set ω : ℝ := Real.sqrt 2 with hωdef
  have hω : ω * ω = 2 := Real.mul_self_sqrt (by norm_num)
  set w : ℝ⟦X⟧ := C ℝ ω with hwdef
  have hw : w ^ 2 = 2 := by
    rw [hwdef, pow_two, ← map_mul, hω, map_ofNat]
  set P : ℝ⟦X⟧ := E ω with hP
  set M : ℝ⟦X⟧ := E (-ω) with hM
  have hPM : P * M = 1 := by rw [hP, hM, E_mul, add_neg_cancel, E_zero]
  have dP : d⁄dX ℝ P = w * P := derivative_E ω
  have dM : d⁄dX ℝ M = -(w * M) := by
    rw [hM, derivative_E, map_neg, neg_mul]
  -- the Riccati solution: `2 A U = V`
  have hQ : 2 * A * ((1 - w) * P + (1 + w) * M) - ((2 - w) * P + (2 + w) * M) = 0 := by
    apply eq_zero_of_derivative_eq_mul (G := 2 * A)
    · have d2 : d⁄dX ℝ (2 : ℝ⟦X⟧) = 0 := by
        rw [show (2 : ℝ⟦X⟧) = C ℝ 2 from (map_ofNat (C ℝ) 2).symm, derivative_C]
      have d1 : d⁄dX ℝ (1 : ℝ⟦X⟧) = 0 := by
        rw [show (1 : ℝ⟦X⟧) = C ℝ 1 from (map_one (C ℝ)).symm, derivative_C]
      have dw : d⁄dX ℝ w = 0 := derivative_C ω
      simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul, dP, dM, d2, d1, dw,
        derivative_A]
      linear_combination (P + M - 2 * A * P - 2 * A * M) * hw
    · simp only [map_sub, map_add, map_mul, constantCoeff_A, hwdef, hP, hM, E, map_ofNat,
        map_one, constantCoeff_C]
      have hc : ∀ c : ℝ, constantCoeff ℝ (rescale c (exp ℝ)) = 1 := by
        intro c
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_exp]
        simp
      rw [hc, hc]
      ring
  have h1 : 2 * A * ((1 - w) * P + (1 + w) * M) = (2 - w) * P + (2 + w) * M :=
    sub_eq_zero.mp hQ
  -- its image under `x ↦ -x`
  set Aσ : ℝ⟦X⟧ := rescale (-1) A with hAσ
  have σP : rescale (-1 : ℝ) P = M := by rw [hP, rescale_E, mul_neg_one]
  have σM : rescale (-1 : ℝ) M = P := by rw [hM, rescale_E, mul_neg_one, neg_neg]
  have σw : rescale (-1 : ℝ) w = w := rescale_C' _ _
  have h2 : 2 * Aσ * ((1 - w) * M + (1 + w) * P) = (2 - w) * M + (2 + w) * P := by
    have := congrArg (rescale (-1 : ℝ)) h1
    simpa only [map_mul, map_add, map_sub, map_ofNat, map_one, σP, σM, σw] using this
  have hUU : ((1 - w) * P + (1 + w) * M) * ((1 - w) * M + (1 + w) * P) = 6 - P ^ 2 - M ^ 2 := by
    linear_combination (2 - P ^ 2 - M ^ 2) * hw + (2 + 2 * w ^ 2) * hPM
  have hVV : ((2 - w) * P + (2 + w) * M) * ((1 - w) * M + (1 + w) * P)
      + ((2 - w) * M + (2 + w) * P) * ((1 - w) * P + (1 + w) * M) = 16 := by
    linear_combination (4 - 2 * P ^ 2 - 2 * M ^ 2) * hw + (8 + 4 * w ^ 2) * hPM
  have hAA : (A + Aσ) * (2 * (6 - P ^ 2 - M ^ 2)) = 16 := by
    linear_combination ((1 - w) * M + (1 + w) * P) * h1 + ((1 - w) * P + (1 + w) * M) * h2
      - 2 * (A + Aσ) * hUU + hVV
  -- the series `B(ω x)`
  set Bt : ℝ⟦X⟧ := rescale ω B with hBt
  have h3 : Bt * (2 - P + M) = 2 := by
    have := congrArg (rescale ω) two_mul_B
    simp only [map_mul, map_add, map_sub, map_ofNat, rescale_E, one_mul, neg_one_mul] at this
    linear_combination this
  set Btσ : ℝ⟦X⟧ := rescale (-1) Bt with hBtσ
  have h4 : Btσ * (2 - M + P) = 2 := by
    have := congrArg (rescale (-1 : ℝ)) h3
    simpa only [map_mul, map_add, map_sub, map_ofNat, σP, σM] using this
  have hBB : (Bt + Btσ) * (2 * (6 - P ^ 2 - M ^ 2)) = 16 := by
    linear_combination (2 * (2 + P - M)) * h3 + (2 * (2 - P + M)) * h4 - 4 * (Bt + Btσ) * hPM
  -- cancel the common factor
  have hW : (2 * (6 - P ^ 2 - M ^ 2) : ℝ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg (constantCoeff ℝ) h0
    have hc : ∀ c : ℝ, constantCoeff ℝ (E c) = 1 := by
      intro c
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_E]
      simp
    simp only [map_mul, map_sub, map_pow, map_ofNat, hP, hM, hc, map_zero] at this
    norm_num at this
  have key : A + Aσ = Bt + Btσ := mul_right_cancel₀ hW (hAA.trans hBB.symm)
  -- compare the coefficients of `x^(2n)`
  have h := congrArg (coeff ℝ (2 * n)) key
  simp only [map_add, hAσ, hBtσ, hBt, coeff_rescale, A, B, coeff_mk] at h
  have hω2 : ω ^ (2 * n) = 2 ^ n := by rw [pow_mul, pow_two, hω]
  have hneg : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hω2, hneg] at h
  have hf : ((2 * n)! : ℝ) ≠ 0 := by positivity
  have hfin : (a (2 * n) : ℝ) = 2 ^ n * b (2 * n) := by
    field_simp at h
    linarith
  exact_mod_cast hfin

end

end MinimaxTrees
