import MABKCore.Quantum
namespace MABK
open Finset
noncomputable section

abbrev Bits (n : ℕ) := Fin n → Bool

def signBit (v : Bool) : ℝ := if v then -1 else 1
def parity {n : ℕ} (a : Bits n) : ℝ := ∏ i, signBit (a i)

theorem parity_square {n : ℕ} (a : Bits n) : (parity a)^2 = 1 := by
  unfold parity
  rw [← Finset.prod_pow]
  have h (i : Fin n) : signBit (a i)^2 = 1 := by cases a i <;> norm_num [signBit]
  simp [h]

theorem parity_sum (n : ℕ) (hn : 0 < n) : ∑ a : Bits n, parity a = 0 := by
  unfold parity
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Bool) => signBit x)]
  simp [Fintype.sum_bool,signBit, hn.ne']

def correlator {n : ℕ} (p : Finset (Fin n) → Bits n → ℝ) (s : Finset (Fin n)) :=
  ∑ a, parity a * p s a

def normalizedScore {n : ℕ} (p : Finset (Fin n) → Bits n → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powerset, (coefficient n s.card).re * correlator p s

def effect {A : Type*} [Ring A] [Algebra ℂ A] (v : A) (a : Bool) : A :=
  algebraMap ℂ A (1/2) * (1+algebraMap ℂ A (signBit a:ℂ)*v)

def outcomeOperator {n : ℕ} {A : Type*} [CStarAlgebra A]
    (P : ProjectiveStrategy n A) (s : Finset (Fin n)) (a : Bits n) : A :=
  word (fun i => effect (P.obs i (decide (i ∈ s))) (a i))

private theorem parity_expansion_comm {n : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B]
    (v : Fin n → B) :
    (∑ a : Bits n, algebraMap ℂ B (parity a:ℂ)*word (fun i => effect (v i) (a i))) =
    word v := by
  classical
  simp only [parity,Complex.ofReal_prod,map_prod,word,Finset.prod_map_toList,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => algebraMap ℂ B (signBit b:ℂ)*effect (v i) b)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  simp only [effect,signBit,Bool.false_eq_true,↓reduceIte,Complex.ofReal_neg,Complex.ofReal_one,
    map_neg,map_one,neg_one_mul,one_mul]
  have h : algebraMap ℂ B (1/2) + algebraMap ℂ B (1/2) = 1 := by
    rw [← map_add,show (1/2:ℂ)+1/2=1 by norm_num,map_one]
  linear_combination v i * h

private theorem parity_expansion {n : ℕ} {A : Type*} [CStarAlgebra A]
    (P : ProjectiveStrategy n A) (s : Finset (Fin n)) :
    (∑ a : Bits n, algebraMap ℂ A (parity a:ℂ)*outcomeOperator P s a) =
    word (fun i => P.obs i (decide (i ∈ s))) := by
  classical
  let v (i : Fin n) := P.obs i (decide (i∈s))
  let B := Algebra.adjoin ℂ (Set.range v)
  letI : CommRing B := Algebra.adjoinCommRingOfComm ℂ (s := Set.range v) (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    by_cases h : i=j
    · rw [h]
    · exact (P.locality i j h _ _).eq)
  let w (i : Fin n) : B := ⟨v i, Algebra.subset_adjoin ⟨i,rfl⟩⟩
  let f := B.val
  have he (y : B) (b : Bool) : f (effect y b) = effect (f y) b := by
    simp only [effect,map_mul,map_add,map_one,AlgHom.commutes]
  have hw (u : Fin n → B) : f (word u) = word (fun i => f (u i)) := by
    simp only [word,map_list_prod,List.map_map]; rfl
  have H := congrArg f (parity_expansion_comm w)
  simp only [map_sum,map_mul,AlgHom.commutes,hw,he] at H
  exact H

theorem born_correlator {n : ℕ} {A : Type*} [CStarAlgebra A]
    (P : ProjectiveStrategy n A) (ω : A →L[ℂ] ℂ) (p : Finset (Fin n) → Bits n → ℝ)
    (born : ∀ s a, ω (outcomeOperator P s a) = (p s a:ℂ)) (s : Finset (Fin n)) :
    ω (word (fun i => P.obs i (decide (i∈s)))) = (correlator p s:ℂ) := by
  rw [← parity_expansion P s,map_sum,correlator,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Algebra.smul_def,map_smul,born,Complex.ofReal_mul,smul_eq_mul]

theorem born_score {n : ℕ} {A : Type*} [CStarAlgebra A]
    (P : ProjectiveStrategy n A) (ω : A →L[ℂ] ℂ) (p : Finset (Fin n) → Bits n → ℝ)
    (born : ∀ s a, ω (outcomeOperator P s a) = (p s a:ℂ)) :
    ω (bellOperator P) = (normalizedScore p:ℂ) := by
  rw [bellOperator,map_sum,normalizedScore,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Algebra.smul_def,map_smul,born_correlator P ω p born,smul_eq_mul,Complex.ofReal_mul]
  rfl

theorem uniform_zero {n : ℕ} (hn : 0 < n) (p : Finset (Fin n) → Bits n → ℝ)
    (uniform : ∀ a, p ∅ a = 1/(2:ℝ)^n) : correlator p ∅ = 0 := by
  simp only [correlator,uniform,← Finset.sum_mul,parity_sum n hn,zero_mul]

theorem abs_upper_from_zero {n : ℕ} {A : Type*} [CStarAlgebra A]
    (P : ProjectiveStrategy n A) (ω : A →L[ℂ] ℂ) (hω : ‖ω‖ ≤ 1)
    (p : Finset (Fin n) → Bits n → ℝ) (born : ∀ s a, ω (outcomeOperator P s a) = (p s a:ℂ))
    (hzero : correlator p ∅ = 0) (disk : TorusDiskClaim n) :
    |normalizedScore p| ≤ radius n := by
  have hh := born_correlator P ω p born ∅
  simp only [Finset.not_mem_empty,Bool.decide_false,hzero,Complex.ofReal_zero] at hh
  have H := projective_bound_of_disk P ω hω hh disk
  rw [born_score P ω p born,Complex.norm_real,Real.norm_eq_abs] at H
  exact H

end
end MABK
