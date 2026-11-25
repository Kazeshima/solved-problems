import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! The normalized CHSH upper bound on the slice with zero first correlator. -/

namespace MABK

open scoped InnerProductSpace

/-- The four vectors can be obtained by acting on a purification with the
two observables of each party and using the real part of the inner product.
Contractions suffice. This lemma also holds for the larger vector model. -/
theorem chsh_zero_correlator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a₀ a₁ b₀ b₁ : H) (ha₀ : ‖a₀‖ ≤ 1) (ha₁ : ‖a₁‖ ≤ 1)
    (hb₀ : ‖b₀‖ ≤ 1) (hb₁ : ‖b₁‖ ≤ 1) (hzero : ⟪a₀, b₀⟫_ℝ = 0) :
    (⟪a₀, b₀⟫_ℝ + ⟪a₀, b₁⟫_ℝ + ⟪a₁, b₀⟫_ℝ - ⟪a₁, b₁⟫_ℝ) / 2 ≤
      3 * Real.sqrt 3 / 4 := by
  let u := (1 / 2 : ℝ) • b₀ + b₁
  let v := b₀ - b₁
  have hu : ⟪a₀, b₁⟫_ℝ ≤ ‖u‖ := by
    calc
      _ = ⟪a₀, u⟫_ℝ := by simp [u, inner_add_right, real_inner_smul_right, hzero]
      _ ≤ ‖a₀‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ha₀ (norm_nonneg _)
      _ = _ := one_mul _
  have hv : ⟪a₁, b₀⟫_ℝ - ⟪a₁, b₁⟫_ℝ ≤ ‖v‖ := by
    calc
      _ = ⟪a₁, v⟫_ℝ := (inner_sub_right ..).symm
      _ ≤ ‖a₁‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ha₁ (norm_nonneg _)
      _ = _ := one_mul _
  have huv : 2 * ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ 9 / 2 := by
    dsimp [u, v]
    rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, real_inner_smul_left]
    norm_num
    nlinarith [sq_nonneg (1 - ‖b₀‖), sq_le_sq' (by linarith [norm_nonneg b₀] : -1 ≤ ‖b₀‖) hb₀,
      sq_le_sq' (by linarith [norm_nonneg b₁] : -1 ≤ ‖b₁‖) hb₁]
  have hs : (‖u‖ + ‖v‖)^2 ≤ (3 * Real.sqrt 3 / 2)^2 := by
    nlinarith [sq_nonneg (2 * ‖u‖ - ‖v‖), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have h := (sq_le_sq₀ (by positivity : 0 ≤ ‖u‖ + ‖v‖) (by positivity)).mp hs
  linarith

end MABK
