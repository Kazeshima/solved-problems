import MABKCore.Outcomes

namespace MABK
open Finset Matrix
open scoped Matrix ComplexConjugate
noncomputable section

abbrev LocalMatrix := Matrix Bool Bool ℂ
abbrev JointMatrix (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

/-- Kronecker product indexed by bit strings, with no arbitrary ordering of basis states. -/
def tensorMatrix {n : ℕ} (M : Fin n → LocalMatrix) : JointMatrix n :=
  fun a b => ∏ i, M i (a i) (b i)

theorem tensor_one (n : ℕ) : tensorMatrix (fun _ : Fin n => 1) = 1 := by
  classical
  ext a b
  by_cases h : a=b
  · subst b; simp [tensorMatrix,Matrix.one_apply]
  · have he : ∃ i, a i ≠ b i := by by_contra! h'; exact h (funext h')
    obtain ⟨i,hi⟩ := he
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem tensor_mul {n : ℕ} (M N : Fin n → LocalMatrix) :
    tensorMatrix M * tensorMatrix N = tensorMatrix (fun i => M i * N i) := by
  ext a b
  simp only [tensorMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => M i (a i) v * N i v (b i))).symm

theorem tensor_star {n : ℕ} (M : Fin n → LocalMatrix) :
    star (tensorMatrix M) = tensorMatrix (fun i => star (M i)) := by
  ext a b
  simp [Matrix.star_apply,tensorMatrix]

def singleMatrix {n : ℕ} (i : Fin n) (M : LocalMatrix) (j : Fin n) : LocalMatrix :=
  if j=i then M else 1

def placeMatrix {n : ℕ} (i : Fin n) (M : LocalMatrix) := tensorMatrix (singleMatrix i M)

theorem place_one {n : ℕ} (i : Fin n) : placeMatrix i 1 = 1 := by
  change tensorMatrix (fun j => if j=i then (1:LocalMatrix) else 1) = 1
  simp only [ite_self,tensor_one]

theorem place_mul {n : ℕ} (i : Fin n) (M N : LocalMatrix) :
    placeMatrix i (M*N) = placeMatrix i M * placeMatrix i N := by
  rw [placeMatrix,placeMatrix,placeMatrix,tensor_mul]
  apply congrArg (@tensorMatrix n); funext j; by_cases h : j=i <;> simp [singleMatrix,h]

theorem place_star {n : ℕ} (i : Fin n) (M : LocalMatrix) :
    star (placeMatrix i M) = placeMatrix i (star M) := by
  rw [placeMatrix,placeMatrix,tensor_star]
  apply congrArg (@tensorMatrix n); funext j; by_cases h : j=i <;> simp [singleMatrix,h]

theorem place_commute {n : ℕ} {i j : Fin n} (h : i ≠ j) (M N : LocalMatrix) :
    Commute (placeMatrix i M) (placeMatrix j N) := by
  change tensorMatrix _ * tensorMatrix _ = tensorMatrix _ * tensorMatrix _
  rw [tensor_mul,tensor_mul]
  apply congrArg (@tensorMatrix n); funext k
  by_cases hi : k=i
  · subst k; simp [singleMatrix,h]
  · simp [singleMatrix,hi]

private theorem place_entries {n : ℕ} (i : Fin n) (M : LocalMatrix) (a b : Bits n) :
    placeMatrix i M a b = M (a i) (b i) * ∏ j ∈ univ.erase i, (1:LocalMatrix) (a j) (b j) := by
  unfold placeMatrix tensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [singleMatrix,if_pos]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem place_add {n : ℕ} (i : Fin n) (M N : LocalMatrix) :
    placeMatrix i (M+N) = placeMatrix i M + placeMatrix i N := by
  ext a b
  simp only [Matrix.add_apply,place_entries]
  rw [add_mul]

theorem place_smul {n : ℕ} (i : Fin n) (c : ℂ) (M : LocalMatrix) :
    placeMatrix i (c • M) = c • placeMatrix i M := by
  ext a b
  simp only [place_entries,Matrix.smul_apply,smul_eq_mul,mul_assoc]

theorem place_effect {n : ℕ} (i : Fin n) (M : LocalMatrix) (a : Bool) :
    placeMatrix i (effect M a) = effect (placeMatrix i M) a := by
  simp only [effect,← Algebra.smul_def,place_smul,place_add,place_one]

theorem word_place {n : ℕ} (M : Fin n → LocalMatrix) :
    word (fun i => placeMatrix i (M i)) = tensorMatrix M := by
  classical
  have aux (l : List (Fin n)) (hl : l.Nodup) :
      (l.map (fun i => placeMatrix i (M i))).prod =
      tensorMatrix (fun j => if j∈l then M j else 1) := by
    induction l with
    | nil => simp [tensor_one]
    | cons i l ih =>
      have hnot := (List.nodup_cons.mp hl).1
      rw [List.map_cons,List.prod_cons,ih (List.nodup_cons.mp hl).2,placeMatrix,tensor_mul]
      apply congrArg (@tensorMatrix n); funext j
      by_cases h : j=i
      · subst j; simp [singleMatrix,hnot]
      · simp [singleMatrix,h]
  simpa only [Finset.mem_toList,Finset.mem_univ,if_true,word] using
    aux (univ : Finset (Fin n)).toList (Finset.nodup_toList _)

end
end MABK
