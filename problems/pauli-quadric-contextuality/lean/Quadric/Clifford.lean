import Quadric.Conventions
import Quadric.Moments

namespace Quadric
open Matrix Finset
open scoped BigOperators

theorem chi_ne_zero (b : Bit) : chi b ≠ 0 := by by_cases h : b=0 <;> simp [chi,h]
theorem chi_one : chi 1 = -1 := by norm_num [chi]

theorem signed_pauli_inj {n} {p r : Label n} {a b : Bit}
    (he : chi a • pauli p = chi b • pauli r) : p=r ∧ a=b := by
  have hs : p=r := by
    by_contra hn
    have ht := congrArg (fun X : Mat n => (pauli p * X).trace) he
    simp only [Matrix.mul_smul,pauli_mul,trace_smul,pauli_trace,smul_eq_mul] at ht
    have hz : p+r≠0 := mt (add_eq_zero_iff_same _ _).mp hn
    simp only [label_self,if_pos rfl,if_neg hz,mul_zero] at ht
    exact (mul_ne_zero (chi_ne_zero _) (mul_ne_zero (chi_ne_zero _) (ne_of_gt (pow_pos (by norm_num : 0 < (2:ℝ)) n)))) ht
  subst r
  have h := congrFun (congrFun he p.1) 0
  exact ⟨rfl,(chi_inj _ _).mp (by simpa [pauli] using h)⟩

/-- An orthogonal real matrix, with its signed action on every real Pauli matrix. -/
structure Clifford (n : ℕ) where
  U : Mat n
  perm : Label n ≃ Label n
  phase : Label n → Bit
  leftInv : Uᵀ * U = 1
  rightInv : U * Uᵀ = 1
  normal (p : Label n) : U * pauli p * Uᵀ = chi (phase p) • pauli (perm p)

namespace Clifford
variable {n : ℕ} 
def conj (C : Clifford n) (A : Mat n) : Mat n := C.U * A * C.Uᵀ
theorem conj_mul (C : Clifford n) (A B : Mat n) :
    C.conj (A*B) = C.conj A * C.conj B := by
  unfold conj
  calc
    _ = C.U * A * (C.Uᵀ*C.U) * B * C.Uᵀ := by rw [C.leftInv]; simp [mul_assoc]
    _ = _ := by noncomm_ring

theorem conj_smul (C : Clifford n) (t : ℝ) (A : Mat n) : C.conj (t • A) = t • C.conj A := by
  simp only [conj, Matrix.mul_smul,Matrix.smul_mul]

theorem conj_one (C : Clifford n) : C.conj 1=1 := by simpa [conj] using C.rightInv

theorem cocycle (C : Clifford n) (p r : Label n) :
    C.perm (p+r) = C.perm p + C.perm r ∧
    cross p r + C.phase (p+r) = C.phase p + C.phase r + cross (C.perm p) (C.perm r) := by
  have h := C.conj_mul (pauli p) (pauli r)
  rw [pauli_mul, C.conj_smul] at h
  change chi (cross p r) • (C.U*pauli (p+r)*C.Uᵀ) = _ at h
  change _ = (C.U*pauli p*C.Uᵀ)*(C.U*pauli r*C.Uᵀ) at h
  rw [C.normal,C.normal,C.normal,Matrix.smul_mul,Matrix.mul_smul,pauli_mul] at h
  simp only [smul_smul,←chi_add] at h
  simpa [add_assoc] using signed_pauli_inj h

@[simp] theorem map_add (C : Clifford n) (p r : Label n) : C.perm (p+r)=C.perm p+C.perm r :=
  (C.cocycle p r).1

@[simp] theorem map_zero (C : Clifford n) : C.perm 0 = 0 := by
  simpa using C.map_add (0:Label n) 0

@[simp] theorem phase_zero (C : Clifford n) : C.phase 0=0 := by
  have h := C.normal 0
  rw [map_zero,identity_pauli,mul_one,C.rightInv] at h
  have hh : chi (0:Bit) • pauli (0 : Label n) = chi (C.phase 0) • pauli (0 : Label n) := by
    simpa [identity_pauli] using h
  exact (signed_pauli_inj hh).2.symm

@[simp] theorem map_q (C : Clifford n) (p : Label n) : q (C.perm p)=q p := by
  have h := (C.cocycle p p).2
  simpa [cross_self,CharTwo.add_self_eq_zero] using h.symm

theorem map_point (C : Clifford n) (p : Label n) : C.perm p ∈ points n ↔ p∈points n := by
  rw [mem_points,mem_points,C.map_q]
  have hh : C.perm p = 0 ↔ p = 0 := by
    have h : C.perm p = C.perm 0 ↔ p=0 := C.perm.injective.eq_iff
    simpa only [C.map_zero] using h
  simp only [ne_eq, hh]

def ident (n : ℕ) : Clifford n where
  U := 1
  perm := Equiv.refl _
  phase := fun _ => 0
  leftInv := by simp
  rightInv := by simp
  normal := by intro p; simp

def mul (C B : Clifford n) : Clifford n where
  U := C.U*B.U
  perm := B.perm.trans C.perm
  phase := fun p => B.phase p+C.phase (B.perm p)
  leftInv := by
    rw [transpose_mul]
    calc
     _ = B.Uᵀ*(C.Uᵀ*C.U)*B.U := by noncomm_ring
     _ = _ := by rw [C.leftInv, mul_one,B.leftInv]
  rightInv := by
    rw [transpose_mul]
    calc
     _ = C.U*(B.U*B.Uᵀ)*C.Uᵀ := by noncomm_ring
     _ = _ := by rw [B.rightInv,mul_one,C.rightInv]
  normal := by
    intro p
    change (C.U*B.U)*pauli p*(C.U*B.U)ᵀ = _
    rw [transpose_mul]
    calc
      _ = C.conj (B.conj (pauli p)) := by unfold conj; noncomm_ring
      _ = _ := by rw [show B.conj (pauli p)=_ from B.normal p,conj_smul,
        show C.conj (pauli (B.perm p))=_ from C.normal _,smul_smul,chi_add]; rfl

def inv (C : Clifford n) : Clifford n where
  U := C.Uᵀ
  perm := C.perm.symm
  phase := fun p => C.phase (C.perm.symm p)
  leftInv := by simpa using C.rightInv
  rightInv := by simpa using C.leftInv
  normal := by
    intro p
    rw [transpose_transpose]
    let q := C.perm.symm p
    have h := C.normal q
    rw [show C.perm q=p from C.perm.apply_symm_apply _] at h
    have hh := congrArg (fun M : Mat n => C.Uᵀ*M*C.U) h
    change C.Uᵀ*(C.U*pauli q*C.Uᵀ)*C.U =
      C.Uᵀ*(chi (C.phase q) • pauli p)*C.U at hh
    have hx : C.Uᵀ*(C.U*pauli q*C.Uᵀ)*C.U = pauli q := by
      calc _ = (C.Uᵀ*C.U)*pauli q*(C.Uᵀ*C.U) := by noncomm_ring
           _ = _ := by rw [C.leftInv,one_mul,mul_one]
    rw [hx,Matrix.mul_smul,Matrix.smul_mul] at hh
    change C.Uᵀ*pauli p*C.U = chi (C.phase q) • pauli q
    rw [hh,smul_smul,chi_sq,one_smul]

end Clifford
end Quadric
