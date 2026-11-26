import Quadric.Lines

namespace Quadric
open Matrix Finset

theorem identity_pauli (n : ℕ) : pauli (0 : Label n) = 1 := by
  ext i j; simp [pauli,Matrix.one_apply]

theorem chi_inj (b c : Bit) : chi b = chi c ↔ b=c := by
  fin_cases b <;> fin_cases c <;> norm_num [chi]

theorem hermitian_iff {n} (p : Label n) :
    (pauli p).IsHermitian ↔ q p = 0 := by
  refine ⟨fun h => ?_,pauli_hermitian⟩
  have he := congrFun (congrFun h.eq p.1) 0
  have hc : chi (q p) = 1 := by
    simpa [pauli,Matrix.conjTranspose_apply,q,dot_comm p.2 p.1] using he
  exact (chi_inj _ 0).mp hc

theorem commute_iff {n} (p r : Label n) :
    Commute (pauli p) (pauli r) ↔ polar p r = 0 := by
  change pauli p * pauli r = pauli r * pauli p ↔ _
  rw [pauli_mul,pauli_mul,add_comm r p]
  have eqsign : chi (cross p r) = chi (cross r p) ↔ polar p r = 0 := by
    rw [chi_inj]
    unfold polar
    constructor
    · rintro he; rw [he,CharTwo.add_self_eq_zero]
    · intro he
      have := congrArg (fun b : Bit => cross p r + b) he
      simpa [← add_assoc,CharTwo.add_self_eq_zero] using this.symm
  constructor
  · intro h
    apply eqsign.mp
    have he := congrFun (congrFun h (p+r).1) 0
    simpa [pauli] using he
  · intro h; rw [eqsign.mpr h]

theorem context_iff_commute {n} {p r : Label n} (hp : p ∈ points n)
    (hr : r ∈ points n) (hne : p ≠ r) :
    (p,r) ∈ pairs n ↔ Commute (pauli p) (pauli r) := by
  have ht : p+r ≠ 0 := mt (add_eq_zero_iff_same p r).mp hne
  simp only [mem_pairs,hp,hr,true_and,mem_points,ht,q_add,(mem_points.mp hp).2,
    (mem_points.mp hr).2,zero_add,commute_iff]
  exact and_iff_right ht

theorem context_product {n} {p r : Label n} (h : (p,r) ∈ pairs n) :
    pauli p * pauli r * pauli (p+r) = chi (cross p r) • (1 : Mat n) := by
  rw [pauli_mul, Matrix.smul_mul, pauli_mul, label_self, identity_pauli,cross_self,
    (mem_points.mp (mem_pairs.mp h).2.2).2,chi_zero,one_smul]

theorem pauli_injective (n : ℕ) : Function.Injective (@pauli n) := by
  intro p r he
  by_contra hne
  have h := congrArg (fun T : Mat n => (pauli p * T).trace) he
  have h0 : p+r ≠ 0 := mt (add_eq_zero_iff_same p r).mp hne
  simp only [pauli_mul,trace_smul,pauli_trace,label_self,if_pos rfl,if_neg h0,
    smul_eq_mul,mul_zero] at h
  have hd : 0 < dim n := by unfold dim; positivity
  by_cases hq : cross p p = 0 <;> simp [chi,hq,hd.ne'] at h

end Quadric
