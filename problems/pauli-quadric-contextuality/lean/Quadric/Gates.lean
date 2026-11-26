import Quadric.Clifford
import Mathlib.Data.Real.Sqrt

namespace Quadric
open Matrix Finset
open scoped BigOperators

theorem pauli_transpose {n} (p : Label n) : (pauli p)ᵀ = chi (q p) • pauli p := by
  ext x y
  change pauli p y x = chi (q p) * pauli p x y
  by_cases h : x=y+p.1
  · subst x
    simp only [pauli,add_assoc,word_self,add_zero,if_pos rfl,dot_add,chi_add,
      dot_comm p.2 p.1,q,if_true]
    ring
  · have h' : y ≠ x+p.1 := fun hh => h (by rw [hh]; simp [add_assoc])
    simp [pauli,h,h']

theorem pauli_swap {n} (p r : Label n) :
    pauli p * pauli r = chi (polar p r) • (pauli r * pauli p) := by
  simp [pauli_mul,smul_smul,←chi_add,polar,add_assoc,CharTwo.add_self_eq_zero, add_comm r p]

theorem pauli_square {n} (p : Label n) : pauli p * pauli p = chi (q p) • (1 : Mat n) := by
  rw [pauli_mul,label_self,identity_pauli,cross_self]

namespace Clifford
variable {n : ℕ}

def ofIntertwine (U : Mat n) (e : Label n ≃ Label n) (δ : Label n → Bit)
    (hL : Uᵀ*U=1) (hR : U*Uᵀ=1)
    (hn : ∀ p, U*pauli p = chi (δ p) • (pauli (e p)*U)) : Clifford n where
  U := U
  perm := e
  phase := δ
  leftInv := hL
  rightInv := hR
  normal p := by rw [hn,Matrix.smul_mul,mul_assoc,hR,mul_one]

def pauliGate (t : Label n) (ht : q t=0) : Clifford n :=
  ofIntertwine (pauli t) (Equiv.refl _) (polar t)
    (by rw [pauli_transpose,ht,chi_zero,one_smul,pauli_square,ht,chi_zero,one_smul])
    (by rw [pauli_transpose,ht,chi_zero,one_smul,pauli_square,ht,chi_zero,one_smul])
    (fun p => pauli_swap t p)

noncomputable def invRoot : ℝ := (Real.sqrt 2)⁻¹
theorem invRoot_sq : invRoot*invRoot=1/2 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  unfold invRoot; field_simp <;> nlinarith

def turnLabel (t p : Label n) := if polar t p = 0 then p else t+p
theorem turn_involution (t : Label n) : Function.Involutive (turnLabel t) := by
  intro p
  have self : polar t (t+p) = polar t p := by
    simp only [polar,cross_add,add_cross,cross_self]
    rw [show q t+cross t p+(q t+cross p t)=
      (q t+q t)+(cross t p + cross p t) by abel,CharTwo.add_self_eq_zero,zero_add]
  by_cases h : polar t p=0 <;> simp [turnLabel,h,self]

noncomputable def rotation (t : Label n) (ht : q t=1) : Clifford n := by
  let J := pauli t
  let U : Mat n := invRoot • (1+J)
  have jt : Jᵀ = -J := by simp [J,pauli_transpose,ht,chi_one]
  have jj : J*J = -1 := by simp [J,pauli_square,ht,chi_one]
  have Ut : Uᵀ = invRoot • (1-J) := by simp [U,transpose_smul,transpose_add,jt,sub_eq_add_neg]
  have scale (A : Mat n) : invRoot • (invRoot • (A+A)) = A := by
    rw [smul_smul,invRoot_sq]; ext i j; simp; ring
  have left : Uᵀ*U=1 := by
    rw [Ut]; change _*(invRoot • (1+J))=_
    rw [Matrix.smul_mul,Matrix.mul_smul]
    have h : (1-J)*(1+J)=(1:Mat n)+1 := by noncomm_ring [jj]
    rw [h,scale]
  have right : U*Uᵀ=1 := by
    rw [Ut]; change (invRoot • (1+J))*_=_
    rw [Matrix.smul_mul,Matrix.mul_smul]
    have h : (1+J)*(1-J)=(1:Mat n)+1 := by noncomm_ring [jj]
    rw [h,scale]
  refine ofIntertwine U (turn_involution t).toPerm
    (fun p => if polar t p=0 then 0 else cross t p) left right ?_
  intro p
  change U*pauli p = chi (if polar t p=0 then 0 else cross t p) •
    (pauli (turnLabel t p)*U)
  by_cases h : polar t p=0
  · have hc : J*pauli p=pauli p*J := by simpa [J,h] using pauli_swap t p
    simp [U,turnLabel,h,Matrix.smul_mul,Matrix.mul_smul,add_mul,mul_add,hc]
  · have hc : J*pauli p= -(pauli p*J) := by simpa [J,chi,h] using pauli_swap t p
    have hs : J*pauli p=chi (cross t p) • pauli (t+p) := pauli_mul _ _
    have hJ : J*pauli p*J=pauli p := by rw [hc,neg_mul,mul_assoc,jj]; simp
    simp only [turnLabel,if_neg h,U,Matrix.smul_mul,Matrix.mul_smul]
    rw [smul_comm (chi _) invRoot]
    apply congrArg (fun M : Mat n => invRoot • M)
    calc
      _ = (J*pauli p)*(1+J) := by simp [add_mul,mul_add,hJ,add_comm]
      _ = _ := by rw [hs,Matrix.smul_mul]

def translation (a : Word n) : Clifford n := pauliGate (a,0) (by simp [q])

noncomputable def hadamard (a b : Word n) (hab : dot a b=1) : Clifford n :=
  (rotation (a,b) hab).mul (pauliGate (0,b) (by simp [q]))

theorem hadamard_matrix (a b : Word n) (hab : dot a b=1) :
    (hadamard a b hab).U = invRoot • (pauli (a,0)+pauli (0,b)) := by
  change (invRoot • (1+pauli (a,b)))*pauli (0,b) = _
  rw [Matrix.smul_mul,add_mul,one_mul,pauli_mul]
  simp [cross,add_comm]

theorem hadamard_symmetric (a b : Word n) (hab : dot a b=1) :
    (hadamard a b hab).Uᵀ = (hadamard a b hab).U := by
  rw [hadamard_matrix]; simp [pauli_transpose,q]

end Clifford
end Quadric
