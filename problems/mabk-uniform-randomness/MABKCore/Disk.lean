import MABKCore.Estimates
import MABKCore.HalfTurn

namespace MABK
open Real Set
noncomputable section

private theorem central_support (n : ℕ) (hn : 4 ≤ n) (x β : ℝ) (hx : |x| ≤ 3*δ n) :
    cos β*(diagonalRe n x - canonicalCenter n) + sin β*diagonalIm n x ≤ radius n := by
  let m := (n:ℝ)+1
  let α := fun y : ℝ => π/4+m*y-β
  let y := fun v : ℝ => (v+β-π/4)/m
  let d := δ n
  let t := canonicalCenter n
  let r := radius n
  let ρ := fun v => (n:ℝ)/m*(cos (y v)^(n-1)+ε n*sin (y v)^(n-1))
  let g := fun v => cos β*(diagonalRe n (y v)-t)+sin β*diagonalIm n (y v)
  have hm : 0 < m := by dsimp [m]; positivity
  have inv₁ (v) : α (y v) = v := by dsimp [α,y]; field_simp [hm.ne']; ring
  have inv₂ (v) : y (α v) = v := by dsimp [α,y]; field_simp [hm.ne']; ring
  have hα : Monotone α := fun _ _ h =>
    sub_le_sub_right (add_le_add_left (mul_le_mul_of_nonneg_left h hm.le) _) _
  have hy : Monotone y := by
    intro u v h
    exact div_le_div_of_nonneg_right (by linarith) hm.le
  have hρ : Continuous ρ := by dsimp [ρ,y]; fun_prop
  have hg (v) : HasDerivAt g (-ρ v * sin v) v := by
    have hy' : HasDerivAt y (1/m) v := by
      simpa [y] using ((((hasDerivAt_id v).add_const β).sub_const (π/4)).div_const m)
    obtain ⟨hre,him⟩ := canonical_tangent n (by omega) (y v)
    convert ((((hre.comp v hy').sub_const t).const_mul (cos β)).add
      ((him.comp v hy').const_mul (sin β))) using 1
    have ha : π/4+((n:ℝ)+1)*y v = v+β := by
      have hh := inv₁ v
      dsimp only [α,m] at hh
      linarith
    simp only [ρ,ha,Real.sin_add,Real.cos_add]
    linear_combination
      ((n:ℝ)/m*(cos (y v)^(n-1)+ε n*sin (y v)^(n-1))*sin v) *
      Real.sin_sq_add_cos_sq β
  have heq : g (α d) = r*cos (α d) := by
    obtain ⟨hre,him⟩ := canonical_contact n
    have ha : α d = π/2-β := by dsimp [α,m,d]; linarith [delta_angle n]
    dsimp only [g]
    rw [inv₂, ha, cos_pi_div_two_sub]
    dsimp [d,t,r]
    rw [hre,him]; ring
  obtain ⟨_,_,hrN⟩ := radius_center_bounds n hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hratio : (n:ℝ)/m ≤ r := (div_le_iff₀ hm).mpr (by dsimp [m,r]; linarith)
  have hr : 0 ≤ r := (div_nonneg hn0 hm.le).trans hratio
  have hd := delta_pos n
  have hds := (delta_bounds n hn).1
  have hdπ : 3*d ≤ π/4 := by dsimp [d]; linarith [pi_gt_d2]
  have hρrange (v) (hv : |y v| ≤ π/4) : 0 ≤ ρ v ∧ ρ v ≤ r := by
    obtain ⟨hlo,hhi⟩ := speed_bounds n hn hv
    have h := div_nonneg hn0 hm.le
    exact ⟨mul_nonneg h hlo, (mul_le_mul_of_nonneg_left hhi h).trans (by rwa [mul_one])⟩
  have hangle : m*d = π/4 := delta_angle n
  obtain ⟨hxl,hxu⟩ := abs_le.mp hx
  have habs : - (π/4) ≤ x ∧ x ≤ π/4 := abs_le.mp (hx.trans hdπ)
  suffices H : g (α x) ≤ r by simpa only [g,inv₂,t,r] using H
  by_cases h : d ≤ x
  · apply (half_turn_support (g:=g) (ρ:=ρ) (hα h) (r:=r) ?_ hr hρ ?_ hg).1 heq
    · apply (hα (show x ≤ 3*d from hxu)).trans
      dsimp only [α]
      rw [show m*(3*d) = 3*(m*d) by ring,hangle]
      linarith [pi_pos]
    · intro v hv
      apply hρrange
      have l := hy hv.1
      have u := hy hv.2
      rw [inv₂] at l u
      exact abs_le.mpr ⟨by dsimp [d] at l; linarith [pi_pos],u.trans habs.2⟩
  · apply (half_turn_support (g:=g) (ρ:=ρ) (hα (le_of_not_ge h)) (r:=r) ?_ hr hρ ?_ hg).2 heq
    · apply le_trans _ (add_le_add_right (hα (show -(3*d) ≤ x from hxl)) π)
      dsimp only [α]
      rw [show m* -(3*d) = -3*(m*d) by ring,hangle]
      linarith
    · intro v hv
      apply hρrange
      have l := hy hv.1
      have u := hy hv.2
      rw [inv₂] at l u
      exact abs_le.mpr ⟨habs.1.trans l,by dsimp [d] at u hdπ; linarith⟩

theorem canonical_disk_norm (n : ℕ) (hn : 4 ≤ n) {x : ℝ} (hx : |x| ≤ π/4) :
    ‖curvePoint n x - (canonicalCenter n : ℂ)‖ ≤ radius n := by
  by_cases h : |x| ≤ 3*δ n
  · let z := curvePoint n x - (canonicalCenter n : ℂ)
    let β := Complex.arg z
    have he : cos β * z.re + sin β * z.im = ‖z‖ := by
      rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
      dsimp only [β]
      nlinarith only [congrArg (fun v : ℝ => ‖z‖*v) (sin_sq_add_cos_sq z.arg)]
    change ‖z‖ ≤ _
    rw [← he]
    simpa [z,curvePoint,Complex.sub_re,Complex.sub_im] using central_support n hn x β h
  · exact outer_disk n hn hx (le_of_not_ge h)

theorem canonical_disk (n : ℕ) (hn : 4 ≤ n) : DiagonalDiskClaim n := by
  intro x hx
  have h := canonical_disk_norm n hn (abs_le.mpr hx)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  simpa [curvePoint,Complex.sub_re,Complex.sub_im,pow_two] using hs

end
end MABK
