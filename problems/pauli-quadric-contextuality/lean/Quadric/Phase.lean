import Quadric.States
import Quadric.Gates
import Mathlib.Data.Matrix.Notation

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators
abbrev Coeff := Fin 10 → Bit

def axis (i : Fin 4) : W := Pi.single i 1
theorem dot_axis (a : W) (i : Fin 4) : dot a (axis i)=a i := by
  simp [dot,axis,Pi.single_apply]

theorem axis_induction (P : W → Prop) (h0 : P 0) (hs : ∀ x i, P x → P (x+axis i)) (x : W) : P x := by
  classical
  have hh (S : Finset (Fin 4)) : P (∑ i ∈ S, Pi.single i (x i)) := by
    induction S using Finset.induction_on with
    | empty => simpa using h0
    | @insert i s hi ih =>
      rw [sum_insert hi,add_comm]
      by_cases h : x i=0
      · simpa [h] using ih
      · have h1 : x i=1 := (by decide : ∀ b:Bit,b≠0 → b=1) _ h
        simpa [h1,axis] using hs _ i ih
  have he : (∑ i, Pi.single i (x i)) = x := by funext j; simp [Pi.single_apply]
  simpa [he] using hh univ

def IsQuadratic (f : W → Bit) : Prop :=
  f 0=0 ∧ ∀ a, ∃ b, ∀ x, f (x+a) = f x + f a + dot b x

def nodes : Fin 10 → W :=
  ![axis 0,axis 1,axis 2,axis 3,axis 0+axis 1,axis 0+axis 2,axis 0+axis 3,
    axis 1+axis 2,axis 1+axis 3,axis 2+axis 3]
def sample (f : W → Bit) : Coeff := fun i => f (nodes i)

def polynomial (c : Coeff) (x : W) : Bit :=
  c 0*x 0+c 1*x 1+c 2*x 2+c 3*x 3+
  (c 4+c 0+c 1)*x 0*x 1+(c 5+c 0+c 2)*x 0*x 2+
  (c 6+c 0+c 3)*x 0*x 3+(c 7+c 1+c 2)*x 1*x 2+
  (c 8+c 1+c 3)*x 1*x 3+(c 9+c 2+c 3)*x 2*x 3

def derivative (c : Coeff) (a : W) : W :=
  ![(c 4+c 0+c 1)*a 1+(c 5+c 0+c 2)*a 2+(c 6+c 0+c 3)*a 3,
    (c 4+c 0+c 1)*a 0+(c 7+c 1+c 2)*a 2+(c 8+c 1+c 3)*a 3,
    (c 5+c 0+c 2)*a 0+(c 7+c 1+c 2)*a 1+(c 9+c 2+c 3)*a 3,
    (c 6+c 0+c 3)*a 0+(c 8+c 1+c 3)*a 1+(c 9+c 2+c 3)*a 2]

theorem polynomial_quad (c : Coeff) : IsQuadratic (polynomial c) := by
  refine ⟨by simp [polynomial],fun a => ⟨derivative c a,fun x => ?_⟩⟩
  simp [polynomial,dot,derivative,Fin.sum_univ_succ]
  ring_nf <;> norm_num

theorem sample_poly (c : Coeff) : sample (polynomial c) = c := by
  funext i; fin_cases i <;>
    simp [sample,nodes,polynomial,axis,Pi.single_apply] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem quadratic_ext {f g : W → Bit} (hf : IsQuadratic f) (hg : IsQuadratic g)
    (h : sample f = sample g) : f=g := by
  have atn (k) : f (nodes k)=g (nodes k) := congrFun h k
  have ax (i : Fin 4) : f (axis i)=g (axis i) := by
    obtain ⟨k,hk⟩ := (by decide : ∀ i : Fin 4, ∃ k, nodes k=axis i) i
    rw [←hk]; exact atn k
  have ax2 (i j : Fin 4) : f (axis j+axis i)=g (axis j+axis i) := by
    by_cases hij : i=j
    · subst j; simp [hf.1,hg.1]
    obtain ⟨k,hk⟩ := (by decide : ∀ i j : Fin 4, i≠j → ∃ k, nodes k=axis j+axis i) i j hij
    rw [←hk]; exact atn k
  funext x
  apply axis_induction (fun y => f y=g y) (hf.1.trans hg.1.symm) _ x
  intro y i hy
  obtain ⟨b,hb⟩ := hf.2 (axis i)
  obtain ⟨c,hc⟩ := hg.2 (axis i)
  have he : b=c := by
    funext j
    have h' := ax2 i j
    rw [hb,hc,dot_axis,dot_axis,ax,ax] at h'
    exact add_left_cancel h'
  rw [hb,hc,he,hy,ax]

abbrev Quadratics := {f : W → Bit // IsQuadratic f}
noncomputable instance : Fintype Quadratics := Fintype.ofFinite _
def phaseCode : Quadratics ≃ Coeff where
  toFun f := sample f.val
  invFun c := ⟨polynomial c,polynomial_quad c⟩
  left_inv f := Subtype.ext (quadratic_ext (polynomial_quad _) f.property (sample_poly _))
  right_inv := sample_poly
theorem phase_count : Fintype.card Quadratics = 1024 := by
  rw [Fintype.card_congr phaseCode]; norm_num [Fintype.card_pi]

noncomputable def phaseGate (f : Quadratics) : Clifford 4 := by
  let b := fun a => (f.property.2 a).choose
  have hb (a x) : f.val (x+a)=f.val x+f.val a+dot (b a) x :=
    (f.property.2 a).choose_spec x
  let U : Mat 4 := diagonal (fun x => chi (f.val x))
  have htr : Uᵀ=U := by simp [U]
  have hi : U*U=1 := by simpa [U,diagonal_mul_diagonal,chi_sq,diagonal_one]
  let T (p : Lab) : Lab := (p.1,p.2+b p.1)
  have Ti : Function.Involutive T := by intro p; ext1 <;> simp [T,add_assoc]
  refine Clifford.ofIntertwine U Ti.toPerm (fun p => f.val p.1)
    (by rw [htr,hi]) (by rw [htr,hi]) ?_
  intro p
  ext y x
  simp only [U,T,mul_diagonal,diagonal_mul,Matrix.smul_apply,smul_eq_mul,pauli]
  change chi (f.val y)*(if y=x+p.1 then _ else 0) =
    chi (f.val p.1)*((if y=x+p.1 then chi (dot (p.2+b p.1) x) else 0)*chi (f.val x))
  by_cases hy : y=x+p.1
  · subst y; rw [if_pos rfl,if_pos rfl,hb,add_dot,chi_add,chi_add,chi_add]; ring
  · simp [hy]

theorem phase_matrix (f : Quadratics) : (phaseGate f).U = diagonal (fun x => chi (f.val x)) := rfl

end Quadric.Four
