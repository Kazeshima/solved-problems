import MABKCore.Curve

namespace MABK
open Real Set
noncomputable section

theorem abs_epsilon (n : ℕ) : |ε n| = 1 := by unfold ε; split <;> norm_num

theorem semicircle_trig {x : ℝ} (hx : |x| ≤ π/4) :
    0 ≤ cos x ∧ |sin x| ≤ cos x := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  have hc := cos_nonneg_of_mem_Icc (show x ∈ Icc (-(π/2)) (π/2) from
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)
  have h2 := cos_nonneg_of_mem_Icc (show 2*x ∈ Icc (-(π/2)) (π/2) from ⟨by linarith,by linarith⟩)
  rw [cos_two_mul'] at h2
  exact ⟨hc, (sq_le_sq₀ (abs_nonneg _) hc).mp (by nlinarith [sq_abs (sin x)])⟩

theorem speed_bounds (n : ℕ) (hn : 4 ≤ n) {x : ℝ} (hx : |x| ≤ π/4) :
    0 ≤ cos x^(n-1) + ε n*sin x^(n-1) ∧
      cos x^(n-1) + ε n*sin x^(n-1) ≤ 1 := by
  obtain ⟨hc,hsc⟩ := semicircle_trig hx
  have hab : |ε n*sin x^(n-1)| = |sin x|^(n-1) := by rw [abs_mul,abs_epsilon,abs_pow,one_mul]
  have hlo := neg_abs_le (ε n*sin x^(n-1))
  have hhi := le_abs_self (ε n*sin x^(n-1))
  rw [hab] at hlo hhi
  have hc2 := pow_le_pow_of_le_one hc (cos_le_one x) (by omega : 2 ≤ n-1)
  have hs2 := pow_le_pow_of_le_one (abs_nonneg _) (hsc.trans (cos_le_one x)) (by omega : 2 ≤ n-1)
  rw [sq_abs] at hs2
  constructor
  · linarith [pow_le_pow_left₀ (abs_nonneg _) hsc (n-1)]
  · linarith [sin_sq_add_cos_sq x]

private theorem pow_cos_lower (n : ℕ) (x : ℝ) :
    1 - (n:ℝ)*x^2/2 ≤ cos x^n := by
  have h := one_add_mul_sub_le_pow (neg_one_le_cos x) n
  nlinarith [mul_le_mul_of_nonneg_left (one_sub_sq_div_two_le_cos (x:=x)) (Nat.cast_nonneg (α:=ℝ) n)]

theorem radius_center_bounds (n : ℕ) (hn : 4 ≤ n) :
    1-(41/100 : ℝ)*δ n < radius n ∧
      |canonicalCenter n| ≤ (101/100 : ℝ)*δ n ∧ (n:ℝ) ≤ ((n:ℝ)+1)*radius n := by
  obtain ⟨hd,_,_,_⟩ := delta_bounds n hn
  have hp := delta_pos n
  have hy : δ n ≤ π/4 := by linarith [pi_gt_d2]
  have hs := sin_nonneg_of_nonneg_of_le_pi hp.le (by linarith [pi_pos])
  have hc := (semicircle_trig (x:=δ n) (by rwa [abs_of_pos hp])).1
  have hs1 := sin_le hp.le
  have hd1 : δ n ≤ 1 := by linarith
  have hsmall3 := pow_le_pow_left₀ hp.le hd.le 3
  have hsmall4 := pow_le_pow_left₀ hp.le hd.le 4
  norm_num at hsmall3 hsmall4
  have hdN : δ n^n ≤ δ n^4 := pow_le_pow_of_le_one hp.le hd1 hn
  have hsn := pow_le_pow_left₀ hs hs1 n
  have hsn1 := pow_le_pow_left₀ hs hs1 (n+1)
  have hpow : sin (δ n)^n ≤ (1/216:ℝ)*δ n := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall3 hp.le]
  have hpow1 : sin (δ n)^(n+1) ≤ (1/1296:ℝ)*δ n := by
    rw [pow_succ (δ n) n] at hsn1
    exact hsn1.trans (mul_le_mul_of_nonneg_right (hdN.trans hsmall4) hp.le)
  have hab : |ε n*sin (δ n)^(n+1)| = sin (δ n)^(n+1) := by
    rw [abs_mul, abs_epsilon, one_mul, abs_of_nonneg (pow_nonneg hs _)]
  have hlo := neg_abs_le (ε n*sin (δ n)^(n+1))
  rw [hab] at hlo
  have hrad : 1-(41/100:ℝ)*δ n < radius n := by
    unfold radius
    have hh := pow_cos_lower (n+1) (δ n)
    push_cast at hh
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt pi_lt_d4) hp.le,
      congrArg (fun a : ℝ => a*δ n) (delta_angle n)]
  refine ⟨hrad, ?_, ?_⟩
  · unfold canonicalCenter
    apply (abs_sub _ _).trans
    simp only [abs_mul,abs_epsilon,abs_of_nonneg hc,abs_of_nonneg hs,abs_pow,one_mul]
    have hcN : cos (δ n)^n ≤ 1 := pow_le_one₀ hc (cos_le_one (δ n))
    nlinarith [mul_le_mul_of_nonneg_left hcN hs,
      mul_le_mul_of_nonneg_right (cos_le_one (δ n)) (pow_nonneg hs n)]
  · have hh := mul_lt_mul_of_pos_left hrad (by positivity : 0 < (n:ℝ)+1)
    nlinarith [delta_angle n,pi_lt_d4]

/-- The elementary inequality cos(y) (1+y²/2) ≤ 1 on the short interval.
Using a reciprocal and Bernoulli avoids an exponential in the outer estimate. -/
private theorem cos_sec_bound {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
    cos y * (1+y^2/2) ≤ 1 := by
  let b := y/2
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb' : b < π/2 := by dsimp [b]; linarith [pi_gt_d2]
  have hc : 0 < cos b := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hb'⟩
  have ht := le_tan hb hb'
  rw [tan_eq_sin_div_cos] at ht
  have hh := (le_div_iff₀ hc).mp ht
  have hsq := sq_le_sq₀ (mul_nonneg hb hc.le) ((mul_nonneg hb hc.le).trans hh) |>.mpr hh
  have he : y = 2*b := by dsimp [b]; ring
  rw [he,cos_two_mul']
  nlinarith [sin_sq_add_cos_sq b, sq_nonneg (b*sin b)]

private theorem cos_outer (n : ℕ) (hn : 4 ≤ n) : cos (3*δ n)^n ≤ 1-3*(n:ℝ)*δ n^2 := by
  have hp := delta_pos n
  obtain ⟨hd,_,hk,_⟩ := delta_bounds n hn
  let y := 3*δ n
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1/2 := by dsimp [y]; linarith
  have hc : 0 ≤ cos y := (semicircle_trig (x:=y) (by rw [abs_of_nonneg hy]; linarith [pi_gt_d2])).1
  have hb := one_add_mul_le_pow (a := y^2/2) (by nlinarith [sq_nonneg y]) n
  have hprod := pow_le_pow_left₀ (mul_nonneg hc (by positivity)) (cos_sec_bound hy hy') n
  rw [mul_pow, one_pow] at hprod
  have hle := mul_le_mul_of_nonneg_left hb (pow_nonneg hc n)
  let k := (n:ℝ)*δ n^2
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk' : k < 1/10 := hk
  have hrel : cos y^n * (1+(9/2:ℝ)*k) ≤ 1 := by
    dsimp [k]; dsimp [y] at hle hprod ⊢; nlinarith only [hle,hprod]
  apply (le_of_mul_le_mul_right (a := 1+(9/2:ℝ)*k) _ (by positivity))
  rw [show 3*(n:ℝ)*δ n^2 = 3*k by dsimp [k]; ring]
  nlinarith [mul_nonneg hk0 (show 0 ≤ 1/10-k by linarith)]

private theorem power_sum_antitone (n : ℕ) (hn : 2 ≤ n) :
    AntitoneOn (fun y => cos y^n+sin y^n) (Icc 0 (π/4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by fun_prop) (by fun_prop)
  intro y hy
  obtain ⟨hy0,hy'⟩ : y ∈ Icc 0 (π/4) := interior_subset hy
  obtain ⟨hc,hsc⟩ := semicircle_trig (x:=y) (by rwa [abs_of_nonneg hy0])
  have hs := sin_nonneg_of_nonneg_of_le_pi hy0 (show y ≤ π by linarith [pi_pos])
  rw [abs_of_nonneg hs] at hsc
  rw [(((hasDerivAt_cos y).pow n).add ((hasDerivAt_sin y).pow n)).deriv]
  have hn' : n-1 = n-2+1 := by omega
  rw [hn',pow_succ,pow_succ]
  have hh := mul_nonneg (show 0 ≤ (n:ℝ)*sin y*cos y by positivity)
    (sub_nonneg.mpr (pow_le_pow_left₀ hs hsc (n-2)))
  nlinarith only [hh]

def curvePoint (n : ℕ) (x : ℝ) : ℂ := ⟨diagonalRe n x,diagonalIm n x⟩

theorem curve_norm_sq (n : ℕ) (x : ℝ) :
    ‖curvePoint n x‖^2 = (cos x^n)^2+(sin x^n)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  dsimp [curvePoint,diagonalRe,diagonalIm]
  let a := π/4 + (n:ℝ)*x
  rw [show π/4 + (n:ℝ)*x = a from rfl]
  nlinarith only [show
    sin a^2*(cos x^n)^2 + cos a^2*(cos x^n)^2 = (cos x^n)^2 by
      nlinarith only [congrArg (fun u : ℝ => u*(cos x^n)^2) (sin_sq_add_cos_sq a)],
    show (ε n)^2*sin a^2*(sin x^n)^2+(ε n)^2*cos a^2*(sin x^n)^2=(sin x^n)^2 by
      rw [epsilon_sq]; nlinarith only [congrArg (fun u : ℝ => u*(sin x^n)^2) (sin_sq_add_cos_sq a)]]

theorem outer_disk (n : ℕ) (hn : 4 ≤ n) {x : ℝ} (hx : |x| ≤ π/4)
    (hout : 3*δ n ≤ |x|) : ‖curvePoint n x - (canonicalCenter n : ℂ)‖ ≤ radius n := by
  obtain ⟨hr,ht,_⟩ := radius_center_bounds n hn
  obtain ⟨hd,hnd,_,_⟩ := delta_bounds n hn
  have hp := delta_pos n
  have h3 : 0 ≤ 3*δ n := by positivity
  have h3' : 3*δ n ≤ π/4 := hout.trans hx
  have hsmall : sin (3*δ n)^n ≤ (3/8:ℝ)*δ n := by
    have hs := sin_nonneg_of_nonneg_of_le_pi h3 (show 3*δ n ≤ π by linarith [pi_pos])
    have h1 := pow_le_pow_left₀ hs (sin_le h3) n
    have h2 := pow_le_pow_of_le_one h3 (show 3*δ n ≤ 1 by linarith) hn
    have h3 := pow_le_pow_left₀ hp.le hd.le 3
    nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
  have hmono := power_sum_antitone n (by omega) (show 3*δ n ∈ Icc 0 (π/4) from ⟨h3,h3'⟩)
    (show |x| ∈ Icc 0 (π/4) from ⟨abs_nonneg _,hx⟩) hout
  have hc := (semicircle_trig hx).1
  have hs := sin_nonneg_of_nonneg_of_le_pi (abs_nonneg x) (show |x| ≤ π by linarith [pi_pos])
  have hsabs : sin |x| = |sin x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hs ⊢
      exact (abs_of_nonneg hs).symm
    · rw [abs_of_neg h, sin_neg] at hs ⊢
      exact (abs_of_nonpos (by linarith)).symm
  have hmod : ‖curvePoint n x‖ ≤ cos |x|^n + sin |x|^n := by
    rw [cos_abs,hsabs]
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (pow_nonneg hc _) (pow_nonneg (abs_nonneg _) _))).mp
    rw [curve_norm_sq,← abs_pow,add_sq,sq_abs]
    nlinarith [mul_nonneg (pow_nonneg hc n) (abs_nonneg (sin x^n))]
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hkk := mul_lt_mul_of_pos_right hnd hp
  dsimp only at hmono
  nlinarith only [hr,ht,hmono,hmod,hsmall,cos_outer n hn,hkk,hp]

end
end MABK
