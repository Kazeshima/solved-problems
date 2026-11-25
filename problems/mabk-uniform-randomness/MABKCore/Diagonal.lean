import MABKCore.Curve
import MABKCore.Estimates
import MABKCore.Symmetry
import MABKCore.Quantum
import MABKCore.Disk

namespace MABK
open Real Finset
open scoped ComplexConjugate
noncomputable section

def cis (x : ℝ) : ℂ := Circle.exp x
def phaseAngle (n : ℕ) : ℝ := ((n:ℝ)-1)*π/4

private theorem cis_parts (x : ℝ) : cis x = (cos x:ℂ)+(sin x:ℂ)*Complex.I := by
  simp [cis,Circle.coe_exp,Complex.exp_mul_I]

private theorem cis_add (x y : ℝ) : cis (x+y) = cis x * cis y := by
  simp [cis,Circle.exp_add]

private theorem cis_conj (x : ℝ) : conj (cis x) = cis (-x) := by
  rw [cis_parts,cis_parts]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,cos_neg,sin_neg,Complex.ofReal_neg]
  ring

private theorem cis_pow (n : ℕ) (x : ℝ) : cis ((n:ℝ)*x) = cis x ^ n := by
  induction n with
  | zero => simp [cis,cis_parts]
  | succ n ih => rw [Nat.cast_succ,add_mul,one_mul,cis_add,ih,pow_succ]

private theorem cis_half : cis (π/2) = Complex.I := by simp [cis_parts]
private theorem cis_pi : cis π = -1 := by simp [cis_parts]
private theorem cis_two_pi : cis (2*π) = 1 := by simp [cis]

private theorem cis_pair (x : ℝ) : cis x + cis (-x) = 2*(cos x:ℂ) := by
  simp [cis_parts]; ring

private theorem split_coefficient (n k : ℕ) :
    coefficient n k = (cis (phaseAngle n)*(-Complex.I)^k +
      cis (-(phaseAngle n))*Complex.I^k)/(2:ℂ)^n := by
  have hn : cis (-(π/2)) = -Complex.I := by simp [cis_parts]
  rw [← hn,← cis_half,← cis_pow,← cis_pow,← cis_add,← cis_add]
  rw [show -phaseAngle n + (k:ℝ)*(π/2) = -(phaseAngle n+(k:ℝ)*(-(π/2))) by ring,cis_pair]
  have ha : phaseAngle n + (k:ℝ)*(-(π/2)) = ((n:ℝ)-1)*π/4-(k:ℝ)*π/2 := by
    unfold phaseAngle; ring
  rw [ha]
  unfold coefficient
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

theorem poly_product (n : ℕ) (z : Fin n → ℂ) :
    poly n z =
      (cis (phaseAngle n)*(∏ i, (1-Complex.I*z i)) +
       cis (-(phaseAngle n))*(∏ i, (1+Complex.I*z i)))/(2:ℂ)^n := by
  classical
  simp only [sub_eq_add_neg,← neg_mul,Finset.prod_one_add,Finset.mul_sum,
    ← Finset.sum_add_distrib,Finset.sum_div]
  unfold poly
  apply Finset.sum_congr rfl
  intro s hs
  change coefficient n s.card * _ = _
  rw [split_coefficient]
  simp only [Finset.prod_mul_distrib,Finset.prod_const]
  ring

private theorem half_factors (x : ℝ) :
    1-Complex.I*cis (π/2+2*x) = 2*cis x*(cos x:ℂ) ∧
    1+Complex.I*cis (π/2+2*x) = -2*Complex.I*cis x*(sin x:ℂ) := by
  have h := cis_add x (-x)
  have h1 : cis x * cis (-x) = 1 := by simpa [cis_parts] using h.symm
  have h2 : cis x - cis (-x) = 2*Complex.I*(sin x:ℂ) := by simp [cis_parts]; ring
  rw [cis_add,cis_half,show 2*x = x+x by ring,cis_add]
  constructor
  · linear_combination -h1 + (cis x) * (cis_pair x) -
      (cis x)^2 * Complex.I_sq
  · linear_combination -h1 + (-cis x) * h2 + (cis x)^2 * Complex.I_sq

private theorem phase_sign (n : ℕ) (hn : Even n) :
    cis (-(phaseAngle n)) * (-Complex.I)^n = cis (phaseAngle n)*Complex.I := by
  have h1 : cis (-(π/2)) = -Complex.I := by simp [cis_parts]
  have hpi : cis (-π) = -1 := by simp [cis_parts]
  rw [← h1,← cis_pow,← cis_add]
  rw [show -(phaseAngle n)+(n:ℝ)*(-(π/2)) = (phaseAngle n+π/2)+(n:ℝ)*(-π) by unfold phaseAngle; ring]
  rw [cis_add,cis_pow,hpi,hn.neg_one_pow,mul_one,cis_add,cis_half]

theorem upper_param (n : ℕ) (hn : Even n) (x : ℝ) :
    poly n (fun _ => cis (π/2+2*x)) =
      cis (phaseAngle n + (n:ℝ)*x)*((cos x:ℂ)^n + Complex.I*(sin x:ℂ)^n) := by
  rw [poly_product]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  obtain ⟨h₁,h₂⟩ := half_factors x
  rw [h₁,h₂,cis_add,cis_pow]
  rw [show -2*Complex.I*cis x*(sin x:ℂ) = 2*(cis x*(sin x:ℂ))*(-Complex.I) by ring]
  simp only [mul_pow]
  apply (div_eq_iff (by norm_num : (2:ℂ)^n ≠ 0)).mpr
  linear_combination ((2:ℂ)^n * cis x^n * (sin x:ℂ)^n) * phase_sign n hn

theorem poly_conj (n : ℕ) (z : Fin n → ℂ) : conj (poly n z) = poly n (fun i => conj (z i)) := by
  unfold poly
  simp only [map_sum,map_mul,map_prod,Complex.conj_ofReal]

theorem canonical_complex (n : ℕ) (x : ℝ) :
    curvePoint n x = cis (π/4+(n:ℝ)*x)*((cos x:ℂ)^n+Complex.I*(ε n:ℂ)*(sin x:ℂ)^n) := by
  rw [cis_parts]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
  apply Complex.ext <;> simp only [curvePoint,diagonalRe,diagonalIm,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im] <;> ring

private theorem phase_mod (n k : ℕ) (h : n%8=k) :
    cis (phaseAngle n) = cis (((k:ℝ)-1)*π/4) := by
  have hn : n = k+8*(n/8) := by omega
  have hnr : (n:ℝ) = (k:ℝ)+8*((n/8:ℕ):ℝ) := by exact_mod_cast hn
  have hp : phaseAngle n = (((k:ℝ)-1)*π/4)+((n/8:ℕ):ℝ)*(2*π) := by
    unfold phaseAngle; rw [hnr]; ring
  rw [hp,cis_add,cis_pow,cis_two_pi,one_pow,mul_one]

def upperValue (n : ℕ) (x : ℝ) := poly n (fun _ => cis (π/2+2*x))

private theorem transform_direct (n : ℕ) (hn : Even n) (x : ℝ) (s : ℂ)
    (h : cis (phaseAngle n) = s*cis (π/4)) (he : ε n = 1) :
    upperValue n x = s * curvePoint n x := by
  rw [upperValue,upper_param n hn,canonical_complex,cis_add,cis_add,h,he]
  push_cast
  ring

private theorem transform_reflected (n : ℕ) (hn : Even n) (x : ℝ) (s : ℂ)
    (h : cis (phaseAngle n) = s*cis (-(π/4))) (he : ε n = -1) :
    upperValue n x = s * conj (curvePoint n (-x)) := by
  rw [upperValue,upper_param n hn,canonical_complex,cis_add,cis_add,h,he]
  simp only [map_mul,map_add,map_pow,cis_conj,cos_neg,sin_neg,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.conj_ofReal,Complex.conj_I,map_neg,map_one,neg_mul,mul_neg,neg_neg,hn.neg_pow]
  ring

theorem residue_table (n : ℕ) (hn : Even n) (x : ℝ) :
    (n%8=0 → upperValue n x = conj (curvePoint n (-x)) ∧ center n = canonicalCenter n) ∧
    (n%8=2 → upperValue n x = curvePoint n x ∧ center n = canonicalCenter n) ∧
    (n%8=4 → upperValue n x = -conj (curvePoint n (-x)) ∧ center n = -canonicalCenter n) ∧
    (n%8=6 → upperValue n x = -curvePoint n x ∧ center n = -canonicalCenter n) := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro h
  · have hp := phase_mod n 0 h
    norm_num at hp
    have he : ε n = -1 := by simp [ε,show n%4 ≠ 2 by omega]
    constructor
    · have hp' : cis (phaseAngle n) = 1*cis (-(π/4)) := by rw [one_mul,hp]; congr 1; ring
      simpa only [one_mul] using transform_reflected n hn x 1 hp' he
    · simp [center,canonicalCenter,h]
  · have hp := phase_mod n 2 h
    norm_num at hp
    have he : ε n = 1 := by simp [ε,show n%4 = 2 by omega]
    constructor
    · simpa using transform_direct n hn x 1 (by simpa using hp) he
    · simp [center,canonicalCenter,h]
  · have hp := phase_mod n 4 h
    norm_num at hp
    have he : ε n = -1 := by simp [ε,show n%4 ≠ 2 by omega]
    constructor
    · have hp' : cis (phaseAngle n) = -1*cis (-(π/4)) := by
        rw [hp,← cis_pi,← cis_add]; congr 1; ring
      simpa only [neg_one_mul] using transform_reflected n hn x (-1) hp' he
    · simp [center,canonicalCenter,h]
  · have hp := phase_mod n 6 h
    norm_num at hp
    have he : ε n = 1 := by simp [ε,show n%4 = 2 by omega]
    constructor
    · have hp' : cis (phaseAngle n) = -1*cis (π/4) := by
        rw [hp,← cis_pi,← cis_add]; congr 1; ring
      simpa only [neg_one_mul] using transform_direct n hn x (-1) hp' he
    · simp [center,canonicalCenter,h]

private theorem even_residues {n : ℕ} (hn : Even n) : n%8=0 ∨ n%8=2 ∨ n%8=4 ∨ n%8=6 := by
  obtain ⟨k,hk⟩ := hn
  omega

private theorem upper_disk (n : ℕ) (hn : Even n) (hn' : 4 ≤ n) {x : ℝ} (hx : |x| ≤ π/4) :
    ‖upperValue n x - (center n:ℂ)‖ ≤ radius n := by
  obtain ⟨h0,h2,h4,h6⟩ := residue_table n hn x
  have hh := canonical_disk_norm n hn' hx
  have hh' := canonical_disk_norm n hn' (x:=-x) (by simpa using hx)
  have hconj : ‖conj (curvePoint n (-x)) - (canonicalCenter n:ℂ)‖ ≤ radius n := by
    calc
      _ = ‖conj (curvePoint n (-x) - (canonicalCenter n:ℂ))‖ := by rw [map_sub,Complex.conj_ofReal]
      _ = _ := Complex.norm_conj _
      _ ≤ _ := hh'
  rcases even_residues hn with h | h | h | h
  · rw [(h0 h).1,(h0 h).2]; exact hconj
  · rw [(h2 h).1,(h2 h).2]; exact hh
  · rw [(h4 h).1,(h4 h).2,Complex.ofReal_neg,neg_sub_neg, norm_sub_rev]; exact hconj
  · rw [(h6 h).1,(h6 h).2,Complex.ofReal_neg,neg_sub_neg, norm_sub_rev]; exact hh

theorem torus_disk (n : ℕ) (hn : Even n) (hn' : 4 ≤ n) : TorusDiskClaim n := by
  apply torusDisk_of_circle (by omega)
  intro u
  let θ := Complex.arg (u:ℂ)
  have hu : cis θ = (u:ℂ) := congrArg (fun x : Circle => (x:ℂ)) (Circle.exp_arg u)
  have upper (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ π) :
      ‖poly n (fun _ => cis a) - (center n:ℂ)‖ ≤ radius n := by
    let x := (a-π/2)/2
    have hx : |x| ≤ π/4 := abs_le.mpr ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
    have h := upper_disk n hn hn' hx
    simpa only [upperValue,show π/2+2*x = a by dsimp [x]; ring] using h
  rw [← hu]
  by_cases h : 0 ≤ θ
  · exact upper θ h (Complex.arg_le_pi _)
  · have hh := upper (-θ) (by linarith) (by dsimp [θ]; linarith [Complex.neg_pi_lt_arg (u:ℂ)])
    have he : conj (poly n (fun _ => cis θ) - (center n:ℂ)) =
        poly n (fun _ => cis (-θ)) - (center n:ℂ) := by rw [map_sub,poly_conj,Complex.conj_ofReal]; simp only [cis_conj]
    simpa only [← he, RCLike.norm_conj] using hh

/-- Eq. (26), written in real arithmetic on each residue class. -/
def angleIndex (n : ℕ) : ℝ :=
  if n%8=2 then (n:ℝ)/4+1/2 else if n%8=4 then (n:ℝ)/4
  else if n%8=6 then 3*(n:ℝ)/4+1/2 else 3*(n:ℝ)/4+1

def publishedAngle (n : ℕ) := 2*π*angleIndex n/((n:ℝ)+1)

theorem angle_contact (n : ℕ) (hn : Even n) :
    (poly n (fun _ => cis (publishedAngle n))).im = radius n := by
  obtain ⟨hre,him⟩ := canonical_contact n
  have hval : (curvePoint n (δ n)).im = radius n := him
  have flip (q : ℝ) : poly n (fun _ => cis (2*π-(π/2+2*q))) = conj (upperValue n q) := by
    rw [upperValue,poly_conj]
    have H := cis_add (2*π) (-(π/2+2*q))
    rw [cis_two_pi,one_mul] at H
    simp only [cis_conj,sub_eq_add_neg,H]
  have hd : (n:ℝ)+1 ≠ 0 := by positivity
  rcases even_residues hn with h | h | h | h
  · have ha : publishedAngle n = 2*π-(π/2+2*(-δ n)) := by
      simp only [publishedAngle,angleIndex,h,δ]; norm_num; field_simp; ring
    rw [ha,flip,((residue_table n hn (-δ n)).1 h).1,neg_neg, starRingEnd_self_apply]
    exact hval
  · have ha : publishedAngle n = π/2+2*δ n := by
      simp only [publishedAngle,angleIndex,h,δ]; norm_num; field_simp; ring
    rw [ha]; change (upperValue n (δ n)).im = _
    rw [((residue_table n hn (δ n)).2.1 h).1]; exact hval
  · have ha : publishedAngle n = π/2+2*(-δ n) := by
      simp only [publishedAngle,angleIndex,h,δ]; norm_num; field_simp; ring
    rw [ha]; change (upperValue n (-δ n)).im = _
    rw [((residue_table n hn (-δ n)).2.2.1 h).1,neg_neg,Complex.neg_im,Complex.conj_im,neg_neg]; exact hval
  · have ha : publishedAngle n = 2*π-(π/2+2*δ n) := by
      simp only [publishedAngle,angleIndex,h,δ]; norm_num; field_simp; ring
    rw [ha,flip,((residue_table n hn (δ n)).2.2.2 h).1,Complex.conj_im,Complex.neg_im,neg_neg]; exact hval

/-- The right-hand side of Eq. (24) after division by the unrestricted quantum maximum. -/
def eq24 (n : ℕ) (θ : ℝ) :=
  cos (θ/2+π/4)^n * sin ((n:ℝ)*θ/2+π/4) +
  cos (θ/2-π/4)^n * sin ((n:ℝ)*θ/2-π/4)

theorem paper_curve (n : ℕ) (θ : ℝ) : (poly n (fun _ => cis θ)).im = eq24 n θ := by
  let a := θ/2+π/4
  let b := θ/2-π/4
  have double (v : ℝ) : 1+cis (2*v) = 2*cis v*(cos v:ℂ) := by
    have H : cis v * cis (-v) = 1 := by rw [← cis_add]; simp [cis]
    rw [show 2*v = v+v by ring,cis_add]
    linear_combination -H + cis v * cis_pair v
  have h₁ : 1-Complex.I*cis θ = 2*cis b*(cos b:ℂ) := by
    rw [← double,show 2*b = -(π/2)+θ by dsimp [b]; ring,cis_add,← cis_conj,cis_half,Complex.conj_I]; ring
  have h₂ : 1+Complex.I*cis θ = 2*cis a*(cos a:ℂ) := by
    rw [← double,show 2*a = π/2+θ by dsimp [a]; ring,cis_add,cis_half]
  have hh : poly n (fun _ => cis θ) =
      cis ((n:ℝ)*θ/2-π/4)*((cos b)^n:ℝ) + cis ((n:ℝ)*θ/2+π/4)*((cos a)^n:ℝ) := by
    rw [poly_product]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,h₁,h₂,mul_pow,Complex.ofReal_pow]
    rw [show (n:ℝ)*θ/2-π/4 = phaseAngle n + (n:ℝ)*b by dsimp [b,phaseAngle]; ring,
      show (n:ℝ)*θ/2+π/4 = -phaseAngle n + (n:ℝ)*a by dsimp [a,phaseAngle]; ring,
      cis_add (phaseAngle n) ((n:ℝ)*b),cis_add (-phaseAngle n) ((n:ℝ)*a),cis_pow,cis_pow]
    apply (div_eq_iff (by norm_num : (2:ℂ)^n ≠ 0)).mpr
    ring
  rw [hh]
  simp only [eq24,cis,Circle.coe_exp,Complex.add_im,Complex.mul_im,Complex.ofReal_im,
    Complex.ofReal_re,Complex.exp_ofReal_mul_I_im,mul_zero,zero_add]
  dsimp [a,b]; ring

end
end MABK
