import MABKCore.Basic

namespace MABK

open Real Set
noncomputable section

theorem delta_pos (n : ℕ) : 0 < δ n := by unfold δ; positivity

theorem delta_angle (n : ℕ) : ((n : ℝ) + 1) * δ n = π / 4 := by
  unfold δ
  field_simp
  ring

theorem delta_bounds (n : ℕ) (hn : 4 ≤ n) :
    δ n < 1/6 ∧ 3/5 < (n : ℝ) * δ n ∧ (n : ℝ) * (δ n)^2 < 1/10 ∧
      ((n : ℝ)+1)*(δ n)^2 < 1/8 := by
  have hN : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h := delta_angle n
  have hd := delta_pos n
  have hp := Real.pi_lt_d4
  have hl := Real.pi_gt_d2
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : δ n < 1/6 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN) hd.le]
  have hscaled : 3/5 < (n : ℝ)*δ n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hd.le]
  have hpi : π^2 < 10 := by nlinarith [Real.pi_pos, mul_self_lt_mul_self Real.pi_pos.le hp]
  have hsq := congrArg (fun x : ℝ => x^2) h
  change (((n:ℝ)+1)*δ n)^2 = (π/4)^2 at hsq
  have hk : (n:ℝ)*(δ n)^2 < 1/10 := by
    have hpoly : 25*(n:ℝ) ≤ 4*((n:ℝ)+1)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN) (show 0 ≤ 4*(n:ℝ)-1 by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hpoly (sq_nonneg (δ n))]
  refine ⟨hsmall, hscaled, hk, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by positivity : 0 ≤ ((n:ℝ)+1)*(δ n)^2)]

theorem epsilon_sq (n : ℕ) : (ε n)^2 = 1 := by unfold ε; split <;> norm_num

theorem canonical_contact (n : ℕ) :
    diagonalRe n (δ n) = canonicalCenter n ∧ diagonalIm n (δ n) = radius n := by
  have ha : π/4 + (n:ℝ)*δ n = π/2 - δ n := by linarith [delta_angle n]
  simp only [diagonalRe, diagonalIm, canonicalCenter, radius, ha, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub, pow_succ]
  constructor <;> ring_nf

/-- Signed tangent vector, in the same real coordinates as the disk predicate. -/
theorem canonical_tangent (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    let a := π/4 + ((n:ℝ)+1)*x
    let R := cos x^(n-1) + ε n*sin x^(n-1)
    HasDerivAt (diagonalRe n) (-(n:ℝ)*sin a*R) x ∧
      HasDerivAt (diagonalIm n) ((n:ℝ)*cos a*R) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  dsimp only
  let b : ℝ → ℝ := fun y => π/4 + ((k+1:ℕ):ℝ)*y
  have hb : HasDerivAt b ((k+1:ℕ):ℝ) x := by
    simpa [b] using ((hasDerivAt_id x).const_mul ((k+1:ℕ):ℝ)).const_add (π/4)
  have hc := (Real.hasDerivAt_cos x).pow (k+1)
  have hs := (Real.hasDerivAt_sin x).pow (k+1)
  have ha : π/4 + (((k+1:ℕ):ℝ)+1)*x = b x + x := by dsimp [b]; ring
  constructor
  · convert ((hb.cos.mul hc).sub (((hb.sin.const_mul (ε (k+1))).mul hs))) using 1
    rw [ha, Real.sin_add]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
    ring
  · convert ((hb.sin.mul hc).add (((hb.cos.const_mul (ε (k+1))).mul hs))) using 1
    rw [ha, Real.cos_add]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
    ring

theorem distance_derivative (n : ℕ) (hn : 1 ≤ n) (t x : ℝ) :
    HasDerivAt (fun y => (diagonalRe n y - t)^2 + (diagonalIm n y)^2)
      (2*(n:ℝ)*(cos x^(n-1) + ε n*sin x^(n-1))*
       (-(sin x)*cos x^n + ε n*cos x*sin x^n + t*sin (π/4+((n:ℝ)+1)*x))) x := by
  obtain ⟨hr, hi⟩ := canonical_tangent n hn x
  convert (((hr.sub_const t).pow 2).add (hi.pow 2)) using 1
  let b := π/4 + (n:ℝ)*x
  have ha : π/4 + ((n:ℝ)+1)*x = b+x := by dsimp [b]; ring
  simp only [diagonalRe, diagonalIm, ha, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [show π/4 + (n:ℝ)*x = b from rfl]
  rw [Real.sin_add b x, Real.cos_add b x]
  linear_combination
    (2*(n:ℝ)*(cos x^(n-1) + ε n*sin x^(n-1))*
      (sin x*cos x^n - ε n*cos x*sin x^n)) * Real.sin_sq_add_cos_sq b

end
end MABK
