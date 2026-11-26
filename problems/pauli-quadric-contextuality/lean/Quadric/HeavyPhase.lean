import Quadric.Action
import Quadric.Phase

namespace Quadric.Four
open Matrix Finset
open scoped BigOperators
attribute [local irreducible] points pairs lines bad violations

def wave (f : W → Bit) (x : W) : ℝ := v x * chi (f x)
def waveMatrix (f : W → Bit) : Mat 4 := (2:ℝ) • ray (wave f) - (3:ℝ) • (1:Mat 4)

theorem phase_image (f : Quadratics) : matrixOf (push (phaseGate f) canonical)=waveMatrix f.val := by
  rw [matrix_push,matrix_canonical,Clifford.conj,candidate,mul_sub,sub_mul,Matrix.mul_smul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,mul_one,(phaseGate f).rightInv]
  rw [show (phaseGate f).U * outer * (phaseGate f).Uᵀ = _ from move_ray (phaseGate f) v]
  have h : (phaseGate f).U *ᵥ v = wave f.val := by
    funext x; rw [phase_matrix]; simp [Matrix.mulVec_diagonal,wave,mul_comm]
  rw [h]; rfl

theorem wave_weight (f : W → Bit) (s : Signing) (hs : matrixOf s=waveMatrix f) (x : W) :
    weight s x = (v x)^2 := by
  dsimp only [weight]; rw [hs]
  by_cases hh : f x=0 <;> simp [waveMatrix,ray,wave,Matrix.one_apply,chi,hh] <;> ring

theorem wave_inj {f g : W → Bit} (hf : f 0=0) (hg : g 0=0)
    (he : waveMatrix f = waveMatrix g) : f=g := by
  funext x
  have h := congrFun (congrFun he x) 0
  change 2 * (wave f x *wave f 0) - 3*(1:Mat 4) x 0 =
    2 * (wave g x*wave g 0) - 3*(1:Mat 4) x 0 at h
  have ha : wave f 0=3 := by simp [wave,v,hf]
  have hb : wave g 0=3 := by simp [wave,v,hg]
  rw [ha,hb] at h
  apply (chi_inj _ _).mp
  by_cases hx : x=0
  · subst x; rw [hf,hg]
  · simp [wave,v,hx] at h; linarith

theorem wave_coeff {s : Signing} {f : W → Bit} (he : matrixOf s=waveMatrix f)
    {a b : W} (hp : (a,b) ∈ points 4) :
    (∑ x, wave f x * wave f (x+a) * chi (dot b x)) = 8*chi (spin s (a,b)) := by
  have hc := coefficient (s:=assign s) hp
  change (matrixOf s * pauli (a,b)).trace = _ at hc
  rw [he,waveMatrix,sub_mul,Matrix.smul_mul,Matrix.smul_mul,one_mul,trace_sub,trace_smul,
    trace_smul,pauli_trace,if_neg (mem_points.mp hp).1,sign_value] at hc
  simp only [smul_eq_mul,mul_zero,sub_zero] at hc
  have htrace : (ray (wave f)*pauli (a,b)).trace =
      ∑ x, wave f x * wave f (x+a) * chi (dot b x) := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,ray,pauli,mul_ite,mul_zero,
      sum_ite_eq',mem_univ,if_true]
  rw [htrace] at hc; linarith

/-- Flat Pauli expectations pin each binary phase derivative to one character. -/
theorem wave_quadratic {s : Signing} {f : W → Bit} (h0 : f 0=0)
    (he : matrixOf s=waveMatrix f) : IsQuadratic f := by
  classical
  refine ⟨h0,fun a => ?_⟩
  by_cases ha : a=0
  · subst a; exact ⟨0,by simp [h0]⟩
  let g (x : W) := chi (f x + f (x+a)+f a)
  have g0 : g 0=1 := by simp [g,h0,CharTwo.add_self_eq_zero]
  have ga : g a=1 := by simp [g,h0,CharTwo.add_self_eq_zero]
  have periodic (x) : g (x+a)=g x := by
    simp only [g,show x+a+a=x by simp [add_assoc]]; rw [add_comm (f (x+a)) (f x)]
  have spectrum (b : W) : walsh g b=0 ∨ walsh g b=16 := by
    by_cases hab : dot a b=0
    · have hp : (a,b) ∈ points 4 := mem_points.mpr ⟨by simp [Prod.ext_iff,ha],hab⟩
      have hs := wave_coeff he hp
      have term' (x : W) : chi (f a)*(wave f x*wave f (x+a)*chi (dot b x)) =
          g x * chi (dot x b) - (if x=0 then 4 else 0) - (if x=a then 4 else 0) := by
        have fact : chi (f a)*(wave f x * wave f (x+a)*chi (dot b x)) =
            v x*v (x+a)*(g x*chi (dot x b)) := by
          simp only [wave,g,chi_add,dot_comm b x]; ring
        rw [fact]
        by_cases hx : x=0
        · subst x; simp [v,ha,g0,Ne.symm ha]; ring
        · by_cases hxa : x=a
          · subst x; simp [v,ha,ga,hab]; ring
          · simp [v,hx,hxa,word_zero]
      have hw : chi (f a)*(8*chi (spin s (a,b))) = walsh g b-8 := by
        rw [←hs,mul_sum]; simp_rw [term',sum_sub_distrib]; simp [walsh]; ring
      by_cases hfa : f a=0 <;> by_cases hsp : spin s (a,b)=0 <;>
        norm_num [chi,hfa,hsp] at hw <;> first | left; linarith | right; linarith
    · left
      have hh := sum_shift a (fun x => g x*chi (dot x b))
      simp only [periodic,add_dot,chi_add,show chi (dot a b) = -1 from by simp [chi,hab],
        mul_neg,mul_one,← sum_neg_distrib] at hh
      change walsh g b=0
      unfold walsh
      rw [sum_neg_distrib] at hh; linarith
  obtain ⟨b,hb⟩ : ∃ b, walsh g b=16 := by
    by_contra! hn
    have hz (b) : walsh g b=0 := (spectrum b).resolve_right (hn b)
    have h := walsh_twice g 0
    change (∑ y, walsh g y*chi (dot y 0)) = 16*g 0 at h
    simp [hz,g0] at h
  refine ⟨b,fun x => ?_⟩
  have hnon (y) : 0 ≤ 1-g y*chi (dot y b) := by
    dsimp [g]; rw [←chi_add]; unfold chi; split_ifs <;> norm_num
  have hsum : ∑ y, (1-g y*chi (dot y b))=0 := by
    rw [sum_sub_distrib,show (∑ y, g y*chi (dot y b))=_ from (rfl : _ = walsh g b),hb]
    norm_num [Fintype.card_pi]
  have hterm := (sum_eq_zero_iff_of_nonneg (fun y _ => hnon y)).mp hsum x (mem_univ x)
  have hm : g x*chi (dot x b)=1 := by linarith
  have hz : g x=chi (dot x b) := by
    calc g x = (g x*chi (dot x b))*chi (dot x b) := by rw [mul_assoc,chi_sq,mul_one]
         _ = _ := by rw [hm,one_mul]
  have ht := (chi_inj _ _).mp hz
  rw [dot_comm b x]
  linear_combination (norm := ring_nf <;> simp [CharTwo.two_eq_zero]) ht

end Quadric.Four
