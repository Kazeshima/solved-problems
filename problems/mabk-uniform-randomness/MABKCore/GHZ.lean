import MABKCore.Diagonal
import MABKCore.Outcomes

namespace MABK
open Real Finset
open scoped ComplexConjugate
noncomputable section

/-- A pure state on the computational tensor basis and two local
orthonormal measurement bases per qubit. The rows are measurement bras. -/
structure QubitExperiment (n : ℕ) where
  ket : Bits n → ℂ
  norm_one : ∑ b, Complex.normSq (ket b) = 1
  bra : Fin n → Bool → Bool → Bool → ℂ
  orthonormal : ∀ i x a a', (∑ b, bra i x a b * conj (bra i x a' b)) =
    if a = a' then 1 else 0

def QubitExperiment.prob {n : ℕ} (M : QubitExperiment n) (s : Finset (Fin n)) (a : Bits n) : ℝ :=
  Complex.normSq (∑ b, M.ket b * ∏ i, M.bra i (decide (i∈s)) (a i) (b i))

private def uhalf : ℝ := (sqrt 2)⁻¹

private theorem uhalf_sq : uhalf^2 = 1/2 := by
  unfold uhalf
  rw [inv_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private theorem uhalf_complex : (uhalf:ℂ)^2 = 1/2 := by rw [← Complex.ofReal_pow,uhalf_sq]; norm_num

private def ghzKet (n : ℕ) (b : Bits n) : ℂ :=
  (if b = (fun _ => false) then (uhalf:ℂ) else 0) +
  (if b = (fun _ => true) then (uhalf:ℂ)*Complex.I else 0)

private theorem ghz_normalized (n : ℕ) (hn : 0 < n) : ∑ b, Complex.normSq (ghzKet n b) = 1 := by
  classical
  let f : Bits n := fun _ => false
  let t : Bits n := fun _ => true
  have hne : f ≠ t := fun he => Bool.false_ne_true (congrFun he ⟨0,hn⟩)
  have h (b : Bits n) : Complex.normSq (ghzKet n b) =
      (if b = f then uhalf^2 else 0) + (if b = t then uhalf^2 else 0) := by
    by_cases h₁ : b = f <;> by_cases h₂ : b = t
    · exact (hne (h₁.symm.trans h₂)).elim
    all_goals
      change Complex.normSq ((if b=f then (uhalf:ℂ) else 0)+(if b=t then (uhalf:ℂ)*Complex.I else 0)) = _
      simp [h₁,h₂,hne,hne.symm,Complex.normSq_ofReal,pow_two]
  simp only [h,Finset.sum_add_distrib]
  simp [uhalf_sq]
  norm_num

private def equatorialBra (θ : ℝ) (x a b : Bool) : ℂ :=
  if b then (uhalf:ℂ) * (signBit a:ℂ) * cis (if x then -θ else 0) else (uhalf:ℂ)

private theorem bra_orthonormal (θ : ℝ) (x a a' : Bool) :
    (∑ b, equatorialBra θ x a b * conj (equatorialBra θ x a' b)) =
    if a = a' then 1 else 0 := by
  let z := cis (if x then -θ else 0)
  have hz : z*conj z = 1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    have hnorm : ‖z‖ = 1 := Circle.norm_coe _
    rw [hnorm]; norm_num
  rw [Fintype.sum_bool]
  change (uhalf:ℂ)*(signBit a:ℂ)*z*conj ((uhalf:ℂ)*(signBit a':ℂ)*z) +
    (uhalf:ℂ)*conj (uhalf:ℂ) = _
  simp only [map_mul,Complex.conj_ofReal]
  have h (p q : ℂ) : (uhalf:ℂ)*p*z*((uhalf:ℂ)*q*conj z) + (uhalf:ℂ)*(uhalf:ℂ) =
      (p*q+1)/2 := by
    linear_combination (uhalf:ℂ)^2*p*q*hz + (p*q+1)*uhalf_complex
  rw [h]
  cases a <;> cases a' <;> norm_num [signBit]

def ghzExperiment (n : ℕ) (hn : 0 < n) (θ : ℝ) : QubitExperiment n where
  ket := ghzKet n
  norm_one := ghz_normalized n hn
  bra := fun _ => equatorialBra θ
  orthonormal := fun _ => bra_orthonormal θ

private theorem cis_zero : cis 0 = 1 := by simp [cis]
private theorem cis_nat (n : ℕ) (x : ℝ) : cis x^n = cis ((n:ℝ)*x) := by
  induction n with
  | zero => simp [cis_zero]
  | succ n ih =>
    rw [pow_succ,ih,Nat.cast_succ,add_mul,one_mul]
    simp [cis,Circle.exp_add]

private theorem amplitude (n : ℕ) (θ : ℝ) (s : Finset (Fin n)) (a : Bits n) :
    (∑ b, ghzKet n b * ∏ i, equatorialBra θ (decide (i∈s)) (a i) (b i)) =
    (uhalf:ℂ)^(n+1)*(1+Complex.I*(parity a:ℂ)*cis (-((s.card:ℝ)*θ))) := by
  classical
  simp only [ghzKet,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,equatorialBra,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Finset.prod_mul_distrib,↓reduceIte,decide_eq_true_eq,Bool.false_eq_true]
  have hphase : (∏ i : Fin n, cis (if i∈s then -θ else 0)) = cis (-((s.card:ℝ)*θ)) := by
    simp only [apply_ite cis,cis_zero,← Finset.prod_filter]
    simp [cis_nat]
  rw [hphase]
  simp only [parity,Complex.ofReal_prod,pow_succ]
  ring

theorem ghz_probability (n : ℕ) (hn : 0 < n) (θ : ℝ) (s : Finset (Fin n)) (a : Bits n) :
    (ghzExperiment n hn θ).prob s a =
      (1+parity a*sin ((s.card:ℝ)*θ))/(2:ℝ)^n := by
  change Complex.normSq (∑ b, ghzKet n b * ∏ i, equatorialBra θ (decide (i∈s)) (a i) (b i)) = _
  rw [amplitude, map_mul, map_pow, Complex.normSq_ofReal]
  let γ := (s.card:ℝ)*θ
  have hc : cis (-γ) = ((cos γ:ℝ):ℂ) - ((sin γ:ℝ):ℂ)*Complex.I := by
    change Complex.exp ((-γ:ℝ)*Complex.I) = _
    rw [Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
    ring
  have hs : Complex.normSq (1+Complex.I*(parity a:ℂ)*cis (-γ)) = 2+2*parity a*sin γ := by
    rw [hc,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im]
    linear_combination (parity a)^2 * Real.sin_sq_add_cos_sq γ + parity_square a
  change (uhalf*uhalf)^(n+1)*Complex.normSq (1+Complex.I*(parity a:ℂ)*cis (-γ)) = _
  rw [hs,← sq,uhalf_sq,pow_succ,div_pow,one_pow]
  dsimp [γ]
  ring

theorem ghz_uniform (n : ℕ) (hn : 0 < n) (θ : ℝ) (a : Bits n) :
    (ghzExperiment n hn θ).prob ∅ a = 1/(2:ℝ)^n := by simp [ghz_probability]

theorem ghz_correlator (n : ℕ) (hn : 0 < n) (θ : ℝ) (s : Finset (Fin n)) :
    correlator (ghzExperiment n hn θ).prob s = sin ((s.card:ℝ)*θ) := by
  unfold correlator
  simp only [ghz_probability]
  let v := sin ((s.card:ℝ)*θ)
  have hh (a : Bits n) : parity a*((1+parity a*v)/(2:ℝ)^n) =
      (parity a+v)/(2:ℝ)^n := by
    apply (eq_div_iff (by positivity)).mpr
    field_simp
    linear_combination v * parity_square a
  change (∑ a : Bits n, parity a*((1+parity a*v)/(2:ℝ)^n)) = v
  simp only [hh,← Finset.sum_div,Finset.sum_add_distrib,parity_sum n hn,zero_add,Finset.sum_const,
    Finset.card_univ]
  simp [Bits,Fintype.card_fun]

theorem ghz_score (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    normalizedScore (ghzExperiment n hn θ).prob =
      (poly n (fun _ => cis θ)).im := by
  unfold normalizedScore poly
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [ghz_correlator, Finset.prod_const,cis_nat,Complex.mul_im]
  simp only [coefficient,cis,Circle.coe_exp,Complex.ofReal_re,Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im,zero_mul,add_zero]

end
end MABK
