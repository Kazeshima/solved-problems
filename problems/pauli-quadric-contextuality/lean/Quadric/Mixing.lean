import Quadric.Action
import Quadric.Gates

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators
attribute [local irreducible] points pairs lines bad violations

abbrev Direction := {a : W // a ≠ 0}

theorem direction_dual (a : Direction) : ∃ b : W, dot a.val b = 1 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp a.property
  refine ⟨Pi.single i 1, ?_⟩
  have h : a.val i ≠ 0 := hi
  have hb : ∀ z : Bit, z ≠ 0 → z=1 := by decide
  simpa [dot, Pi.single_apply] using hb _ h

noncomputable def dual (a : Direction) : W := (direction_dual a).choose
theorem dot_dual (a : Direction) : dot a.val (dual a)=1 := (direction_dual a).choose_spec
noncomputable def mixGate (a : Direction) := Clifford.hadamard a.val (dual a) (dot_dual a)
noncomputable def step (a : Direction) (s : Opt) := optMove (mixGate a) s

theorem step_involutive (a : Direction) : Function.Involutive (step a) := by
  intro s
  apply Subtype.ext
  apply matrix_injective
  change matrixOf (push (mixGate a) (push (mixGate a) s.val))=_
  rw [matrix_push,matrix_push]
  let C := mixGate a
  have hs : C.Uᵀ=C.U := Clifford.hadamard_symmetric _ _ _
  have hs2 : C.U*C.U = 1 := by simpa [hs] using C.leftInv
  change C.U*(C.U*matrixOf s.val*C.Uᵀ)*C.Uᵀ=_
  rw [hs]
  calc
    _ = (C.U*C.U)*matrixOf s.val*(C.U*C.U) := by noncomm_ring
    _ = _ := by rw [hs2,one_mul,mul_one]

theorem pauli_apply_vec {n} (p : Label n) (u : Word n → ℝ) (x : Word n) :
    (pauli p *ᵥ u) x = chi (dot p.2 (x+p.1))*u (x+p.1) := by
  change (∑ j, (if x=j+p.1 then chi (dot p.2 j) else 0)*u j) = _
  have eq (j : Word n) : x=j+p.1 ↔ j=x+p.1 := by
    constructor <;> rintro rfl <;> simp [add_assoc]
  simp [eq,ite_mul]

theorem mix_vec (a : Direction) (u : W → ℝ) (x : W) :
    ((mixGate a).U *ᵥ u) x = Clifford.invRoot * (u (x+a.val) + chi (dot (dual a) x)*u x) := by
  rw [mixGate,Clifford.hadamard_matrix,Matrix.smul_mulVec_assoc,Matrix.add_mulVec]
  simp [pauli_apply_vec]

theorem word_twice (x a : W) : x+a+a=x := by simp [add_assoc]

def PairCode (m j b c : Fin 10) : Prop :=
  b.val+c.val=m.val+j.val ∧ ((b.val:ℤ)-c.val)^2 = 4*(m.val:ℤ)*j.val
instance (m j b c : Fin 10) : Decidable (PairCode m j b c) := by unfold PairCode; infer_instance

def Compatible (m j : Fin 10) := ∃ b c, PairCode m j b c
instance (m j : Fin 10) : Decidable (Compatible m j) := by unfold Compatible; infer_instance

theorem mix_levels (a : Direction) (s : Opt) (x : W) :
    PairCode (level s x) (level s (x+a.val)) (level (step a s) x) (level (step a s) (x+a.val)) := by
  obtain ⟨u,_,hu⟩ := state_ray s
  have hm := move_ray_formula (mixGate a) hu
  let x' := x+a.val
  let v := u x
  let w := u x'
  let z := chi (dot (dual a) x)
  let c := Clifford.invRoot
  have hh : c^2=1/2 := by simpa only [sq] using Clifford.invRoot_sq
  have hz : z^2=1 := by simpa only [sq] using chi_sq (dot (dual a) x)
  have hneg : chi (dot (dual a) (x+a.val)) = -z := by
    rw [dot_add,dot_comm (dual a) a.val,dot_dual,chi_add,chi_one]; ring
  have hi : ((level s x).val : ℝ)=24*v^2 := (level_spec s _).symm.trans (weight_of_ray hu _)
  have hj : ((level s x').val : ℝ)=24*w^2 := (level_spec s _).symm.trans (weight_of_ray hu _)
  have hb : ((level (step a s) x).val : ℝ) = 24*(c*(w+z*v))^2 := by
    rw [←level_spec]
    exact (weight_of_ray hm _).trans (by rw [mix_vec])
  have hc : ((level (step a s) x').val : ℝ)=24*(c*(v-z*w))^2 := by
    rw [←level_spec]
    exact (weight_of_ray hm _).trans (by
      dsimp only [x']; rw [mix_vec,word_twice,hneg]; dsimp [v,w,z,c,x']; ring)
  have hb' : ((level (step a s) x).val : ℝ)=12*(w+z*v)^2 := by
    rw [hb,mul_pow,hh]; ring
  have hc' : ((level (step a s) x').val : ℝ)=12*(v-z*w)^2 := by
    rw [hc,mul_pow,hh]; ring
  constructor
  · exact_mod_cast (show ((level (step a s) x).val : ℝ)+ (level (step a s) x').val =
      (level s x).val + (level s x').val by
        rw [hb',hc',hi,hj]; ring_nf; rw [hz]; ring)
  · exact_mod_cast (show (((level (step a s) x).val : ℝ)-(level (step a s) x').val)^2 =
      4*((level s x).val : ℝ)*(level s x').val by
        rw [hb',hc',hi,hj]
        have dif : 12*(w+z*v)^2-12*(v-z*w)^2=48*z*v*w := by
          ring_nf; rw [hz]; ring
        rw [dif]; ring_nf; rw [hz]; ring)

theorem compatible_coords (s : Opt) {x y : W} (h : x≠y) : Compatible (level s x) (level s y) := by
  let a : Direction := ⟨x+y,mt (word_zero x y).mp h⟩
  have he : x+a.val=y := by dsimp [a]; simp [←add_assoc]
  exact ⟨_,_,he ▸ mix_levels a s x⟩

end Quadric.Four
