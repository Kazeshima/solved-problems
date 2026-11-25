import MABKCore.Tensor
import MABKCore.GHZ

namespace MABK
open Finset Matrix
open scoped ComplexConjugate InnerProductSpace
noncomputable section

/-- A normalized pure state on a Hilbert space. Taking a purification includes
mixed states and an unmeasured environment. -/
def vectorState {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ψ).comp (ContinuousLinearMap.apply ℂ H ψ)

theorem vectorState_contractive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (hψ : ‖ψ‖ = 1) : ‖vectorState ψ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  change ‖⟪ψ,X ψ⟫_ℂ‖ ≤ 1*‖X‖
  calc
    _ ≤ ‖ψ‖*‖X ψ‖ := norm_inner_le_norm _ _
    _ ≤ _ := by rw [hψ,one_mul,one_mul]; simpa [hψ] using X.le_opNorm ψ

/-- This is the standard projective Hilbert-space Born model. Locality is
expressed by interparty commutation, which includes tensor-product devices. -/
structure HilbertBehavior (n : ℕ) where
  H : Type
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  ψ : H
  norm_one : ‖ψ‖ = 1
  P : ProjectiveStrategy n (H →L[ℂ] H)

attribute [instance] HilbertBehavior.normed HilbertBehavior.innerSpace HilbertBehavior.complete

def HilbertBehavior.Realizes {n : ℕ} (e : HilbertBehavior n) (p : Finset (Fin n) → Bits n → ℝ) :=
  ∀ s a, vectorState e.ψ (outcomeOperator e.P s a) = (p s a:ℂ)

private def proj {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x a : Bool) : LocalMatrix :=
  fun b c => conj (M.bra i x a b)*M.bra i x a c

private theorem proj_star {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x a : Bool) :
    star (proj M i x a) = proj M i x a := by
  ext b c
  change conj (conj (M.bra i x a c)*M.bra i x a b) = _
  simp [proj,mul_comm]

private theorem proj_mul {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x a a' : Bool) :
    proj M i x a * proj M i x a' = if a=a' then proj M i x a else 0 := by
  ext b c
  rw [Matrix.mul_apply]
  have h (k) : proj M i x a b k * proj M i x a' k c =
      (conj (M.bra i x a b)*M.bra i x a' c) *
      (M.bra i x a k*conj (M.bra i x a' k)) := by unfold proj; ring
  simp only [h,← Finset.mul_sum,M.orthonormal]
  by_cases ha : a=a' <;> simp [ha,proj]

private theorem proj_sum {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x : Bool) :
    proj M i x false + proj M i x true = 1 := by
  let U : LocalMatrix := M.bra i x
  have hr : U * star U = 1 := by
    ext b c
    change (∑ k, M.bra i x b k * conj (M.bra i x c k)) = _
    rw [M.orthonormal,Matrix.one_apply]
  have hc := Matrix.mul_eq_one_comm.mp hr
  ext b c
  have H := congrFun (congrFun hc b) c
  change (∑ k, conj (M.bra i x k b)*M.bra i x k c) = _ at H
  rw [Fintype.sum_bool] at H
  simpa only [proj,Matrix.add_apply,add_comm] using H

private def obs {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x : Bool) : LocalMatrix :=
  proj M i x false - proj M i x true

private theorem obs_star {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x : Bool) :
    star (obs M i x) = obs M i x := by simp only [obs,star_sub,proj_star]

private theorem obs_invol {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x : Bool) :
    obs M i x * obs M i x = 1 := by
  simp only [obs,sub_mul,mul_sub,proj_mul,if_true,if_false,Bool.false_eq_true,
    Bool.true_eq_false,sub_zero,zero_sub,sub_neg_eq_add,proj_sum]

private theorem obs_effect {n : ℕ} (M : QubitExperiment n) (i : Fin n) (x a : Bool) :
    effect (obs M i x) a = proj M i x a := by
  simp only [effect,← Algebra.smul_def,obs]
  rw [← proj_sum M i x]
  ext b c
  cases a <;> simp only [Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,smul_eq_mul,
    signBit,Bool.false_eq_true,↓reduceIte,Complex.ofReal_neg,Complex.ofReal_one] <;> ring

abbrev QubitSpace (n : ℕ) := EuclideanSpace ℂ (Bits n)

private def asOperator (n : ℕ) : JointMatrix n →⋆ₐ[ℂ] (QubitSpace n →L[ℂ] QubitSpace n) :=
  Matrix.toEuclideanCLM (n:=Bits n) (𝕜:=ℂ)

private def qubitPVM {n : ℕ} (M : QubitExperiment n) : ProjectiveStrategy n (QubitSpace n →L[ℂ] QubitSpace n) where
  obs i x := asOperator n (placeMatrix i (obs M i x))
  selfAdjoint i x := by rw [← map_star,place_star,obs_star]
  unitary_mem i x := by
    have hs : star (asOperator n (placeMatrix i (obs M i x))) = asOperator n (placeMatrix i (obs M i x)) := by
      rw [← map_star,place_star,obs_star]
    have hh : asOperator n (placeMatrix i (obs M i x)) * asOperator n (placeMatrix i (obs M i x)) = 1 := by
      rw [← map_mul,← place_mul,obs_invol,place_one,map_one]
    exact ⟨by rwa [hs],by rwa [hs]⟩
  locality i j hij x y := (place_commute hij (obs M i x) (obs M j y)).map (asOperator n)

private theorem outcome_tensor {n : ℕ} (M : QubitExperiment n) (s : Finset (Fin n)) (a : Bits n) :
    outcomeOperator (qubitPVM M) s a =
    asOperator n (tensorMatrix (fun i => proj M i (decide (i∈s)) (a i))) := by
  have hm (v : JointMatrix n) (b : Bool) : asOperator n (effect v b) = effect (asOperator n v) b := by
    simp only [effect,map_add,map_mul,map_one,AlgHomClass.commutes]
  have hw (u : Fin n → JointMatrix n) : asOperator n (word u) = word (fun i => asOperator n (u i)) := by
    simp only [word,map_list_prod,List.map_map]; rfl
  rw [← word_place,hw]
  unfold outcomeOperator
  congr 1
  funext i
  change effect (asOperator n (placeMatrix i (obs M i _))) (a i) = _
  rw [← hm,← place_effect,obs_effect]

private def qubitKet {n : ℕ} (M : QubitExperiment n) : QubitSpace n :=
  (WithLp.equiv 2 _).symm M.ket

private theorem qubitKet_one {n : ℕ} (M : QubitExperiment n) : ‖qubitKet M‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [qubitKet,Complex.sq_norm,one_pow]
  exact M.norm_one

/-- Every pure product-basis qubit experiment defined by tensor amplitudes
has the same probabilities in the general Hilbert-space model. -/
theorem tensor_realization {n : ℕ} (M : QubitExperiment n) :
    ∃ e : HilbertBehavior n, e.Realizes M.prob := by
  let e : HilbertBehavior n := {
    H := QubitSpace n
    ψ := qubitKet M
    norm_one := qubitKet_one M
    P := qubitPVM M }
  refine ⟨e,?_⟩
  intro s a
  change ⟪qubitKet M,outcomeOperator (qubitPVM M) s a (qubitKet M)⟫_ℂ = _
  rw [outcome_tensor]
  let row (b : Bits n) : ℂ := ∏ i, M.bra i (decide (i∈s)) (a i) (b i)
  let K := tensorMatrix (fun i => proj M i (decide (i∈s)) (a i))
  have hK (b c : Bits n) : K b c = conj (row b)*row c := by
    simp only [K,tensorMatrix,proj,row,Finset.prod_mul_distrib,map_prod]
  let u : ℂ := ∑ b, M.ket b*row b
  change ⟪(WithLp.equiv 2 _).symm M.ket, Matrix.toEuclideanCLM (n:=Bits n) (𝕜:=ℂ) K ((WithLp.equiv 2 _).symm M.ket)⟫_ℂ =
    (Complex.normSq u:ℂ)
  rw [Matrix.toEuclideanCLM_piLp_equiv_symm,EuclideanSpace.inner_piLp_equiv_symm,Matrix.toLin'_apply]
  change (∑ b, (∑ c, K b c * M.ket c) * conj (M.ket b)) = _
  have hr (b) : (∑ c, K b c * M.ket c) = conj (row b)*u := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; rw [hK]; ring
  simp only [hr]
  calc
    _ = u * conj u := by
      change _ = u * conj (∑ b, M.ket b*row b)
      rw [map_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _; rw [map_mul]; ring
    _ = _ := Complex.mul_conj _

end
end MABK
