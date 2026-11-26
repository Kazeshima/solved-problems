import Quadric.Asymptotic

namespace Quadric.Five

theorem lines_card : (lines 5).card = 23715 := by
  have h := line_count 5
  norm_num [dim] at h
  exact_mod_cast (by linarith : ((lines 5).card : ℝ) = 23715)

/-- The rounded all-rank spectral bound at five qubits. -/
theorem spectral_lower : 6426 ≤ degree 5 := by
  have h := (contextuality_bounds 5 (by decide)).1
  norm_num [dim,fraction,lines_card] at h
  by_contra! hb
  have hn : degree 5 ≤ 6425 := by omega
  have hc : (degree 5 : ℝ) ≤ 6425 := by exact_mod_cast hn
  have hs : (Real.sqrt 68)^2=68 := Real.sq_sqrt (by norm_num)
  have hc' : Real.sqrt 68 ≤ (82463:ℝ)/10000 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [hs]; norm_num
  linarith

end Quadric.Five
