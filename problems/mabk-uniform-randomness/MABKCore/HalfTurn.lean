import Mathlib

namespace MABK
open Real Set MeasureTheory intervalIntegral
noncomputable section

private theorem abs_sin_half_turn (a : ℝ) : (∫ x in a..a+π, |sin x|) = 2 := by
  have hp : Function.Periodic (fun x : ℝ => |sin x|) π := by intro x; simp
  rw [hp.intervalIntegral_add_eq a 0, zero_add]
  have h : (∫ x in (0:ℝ)..π, |sin x|) = ∫ x in (0:ℝ)..π, sin x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le pi_pos.le] at hx
    exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)
  rw [h, integral_sin, cos_zero, cos_pi]
  norm_num

/-- Over at most half a turn, a tangent whose radius of curvature lies
between 0 and r stays in a disk of radius r tangent at either endpoint.
Here g is its projection onto an arbitrary unit direction, and the angular
parameter is measured from that direction. -/
theorem half_turn_support {g ρ : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hshort : b ≤ a+π) (hr : 0 ≤ r) (hc : Continuous ρ)
    (hρ : ∀ x ∈ Icc a b, 0 ≤ ρ x ∧ ρ x ≤ r)
    (hg : ∀ x, HasDerivAt g (-ρ x * sin x) x) :
    (g a = r*cos a → g b ≤ r) ∧ (g b = r*cos b → g a ≤ r) := by
  let q := fun x => g x - r/2*cos x
  let v := fun x => (r/2 - ρ x)*sin x
  have hv : Continuous v := by unfold v; fun_prop
  have hq (x) : HasDerivAt q (v x) x := by
    convert (hg x).sub ((hasDerivAt_cos x).const_mul (r/2)) using 1
    dsimp [v]
    ring
  have hdiff := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc a b) => hq x) (hv.intervalIntegrable a b)
  have hcabs : Continuous fun x : ℝ => |sin x| := continuous_sin.abs
  have hbnd : |q b-q a| ≤ (r/2)*(∫ x in a..b, |sin x|) := by
    rw [← hdiff, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    apply intervalIntegral.integral_mono_on hab (hv.abs.intervalIntegrable _ _)
      ((continuous_const.mul hcabs).intervalIntegrable _ _)
    intro x hx
    obtain ⟨h₁,h₂⟩ := hρ x hx
    dsimp [v]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
  have hrest : cos b+cos a ≤ ∫ x in b..a+π, |sin x| := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hshort (continuous_sin.intervalIntegrable b (a+π))
      (hcabs.intervalIntegrable _ _) (fun x _ => le_abs_self (sin x))
    simpa [integral_sin, sub_eq_add_neg] using h
  have hwhole := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcabs.intervalIntegrable a b) (hcabs.intervalIntegrable b (a+π))
  rw [abs_sin_half_turn] at hwhole
  have hcom : (r/2)*(cos b+cos a+(∫ x in a..b, |sin x|)) ≤ r := by
    have hh : cos b+cos a+(∫ x in a..b, |sin x|) ≤ 2 := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r/2)]
  obtain ⟨hlo,hhi⟩ := abs_le.mp hbnd
  dsimp [q] at hlo hhi
  constructor <;> intro heq <;> nlinarith only [heq,hcom,hlo,hhi]

end
end MABK
