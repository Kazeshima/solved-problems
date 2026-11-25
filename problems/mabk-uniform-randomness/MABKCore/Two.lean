import MABKCore.Diagonal

namespace MABK
open Real Finset
open scoped ComplexConjugate
noncomputable section

private theorem two_constants :
    center 2 = cos (π/4)/4 ∧ 0 ≤ radius 2 ∧ (radius 2)^2 = 27/32 := by
  let c := cos (δ 2)
  let s := sin (δ 2)
  have hd : δ 2 = π/12 := by norm_num [δ]
  have hsum : s^2+c^2=1 := sin_sq_add_cos_sq _
  have hcs : c*s=1/4 := by
    have h := sin_two_mul (δ 2)
    rw [show 2*δ 2 = π/6 by rw [hd]; ring,sin_pi_div_six] at h
    dsimp [c,s]; linarith
  have hc := (semicircle_trig (x:=δ 2) (by rw [abs_of_pos (delta_pos 2),hd]; linarith [pi_pos])).2
  have hs0 : 0 ≤ s := sin_nonneg_of_nonneg_of_le_pi (delta_pos 2).le (by rw [hd]; linarith [pi_pos])
  have hsc : s ≤ c := (le_abs_self _).trans hc
  have hcos : cos (π/4)^2 = 1/2 := by rw [cos_pi_div_four]; nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hdif : c-s = cos (π/4) := by
    have hpos : 0 ≤ cos (π/4) := by rw [cos_pi_div_four]; positivity
    apply (sq_eq_sq₀ (sub_nonneg.mpr hsc) hpos).mp
    nlinarith
  have he : ε 2 = 1 := by norm_num [ε]
  have hr : radius 2 = (c+s)*(3/4) := by
    simp only [radius,he,one_mul]; change c^3+s^3 = _
    linear_combination (c+s)*hsum - (c+s)*hcs
  refine ⟨?_,?_,?_⟩
  · simp only [center,he,one_mul]; norm_num
    change s*c^2-c*s^2 = _
    rw [cos_pi_div_four] at hdif
    rw [← hdif]; linear_combination (c-s)*hcs
  · rw [hr]; exact mul_nonneg (by linarith) (by norm_num)
  · rw [hr]; nlinarith

private theorem poly_two (u : ℂ) :
    poly 2 (fun _ => u) = (cos (π/4):ℂ)/2*(1+2*u-u^2) := by
  rw [poly_product]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have ha : phaseAngle 2 = π/4 := by norm_num [phaseAngle]
  rw [ha]
  have hphase (x : ℝ) : cis x = (Real.cos x:ℂ)+(Real.sin x:ℂ)*Complex.I := by
    simp [cis,Circle.coe_exp,Complex.exp_mul_I]
  rw [hphase,hphase]
  simp only [cos_neg,sin_neg,Complex.ofReal_neg,sin_pi_div_four,cos_pi_div_four]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem torus_disk_two : TorusDiskClaim 2 := by
  apply torusDisk_of_circle (by decide)
  intro u
  obtain ⟨ht,hr,hrs⟩ := two_constants
  let a := cos (π/4)
  have ha : a^2 = 1/2 := by dsimp [a]; rw [cos_pi_div_four]; nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  let z := (u:ℂ)
  have hz : ‖z‖ = 1 := u.norm_coe
  have hz2 := Complex.sq_norm_sub_sq_re z
  rw [hz] at hz2
  have hmul : z * conj z = 1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]; norm_num
  let p := poly 2 (fun _ => z) - (center 2:ℂ)
  have hpoly : p*conj z = (a:ℂ)/2*(2 + conj z/2-z) := by
    dsimp only [p]; rw [poly_two,ht,Complex.ofReal_div,Complex.ofReal_ofNat]
    change (↑a/2*(1+2*z-z^2)-↑a/4)*conj z = _
    linear_combination ((a:ℂ) - (a:ℂ)/2*z) * hmul
  have hn : ‖p*conj z‖ = ‖p‖ := by rw [norm_mul,RCLike.norm_conj,hz,mul_one]
  change ‖p‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) hr).mp
  rw [← hn,hpoly,hrs,Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    Complex.re_ofNat,Complex.im_ofNat]
  have he : (a/2*(2+z.re/2-z.re))^2 + (a/2*(-z.im/2-z.im))^2 =
      27/32-(z.re+1/2)^2/4 := by
    linear_combination ((2-z.re/2)^2 + (3*z.im/2)^2)/4 * ha - (9/32)*hz2
  nlinarith only [he, sq_nonneg (z.re+1/2)]

end
end MABK
