import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace Quadric
open scoped BigOperators
open Finset Matrix

abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := Fin n → Bit
abbrev Label (n : ℕ) := Word n × Word n
abbrev Mat (n : ℕ) := Matrix (Word n) (Word n) ℝ

def dim (n : ℕ) : ℝ := 2 ^ n

def dot {n} (a b : Word n) : Bit := ∑ i, a i * b i
def q {n} (p : Label n) : Bit := dot p.1 p.2
def cross {n} (p r : Label n) : Bit := dot p.2 r.1
def polar {n} (p r : Label n) : Bit := cross p r + cross r p

def chi (b : Bit) : ℝ := if b = 0 then 1 else -1
@[simp] theorem chi_zero : chi 0 = 1 := rfl
theorem chi_add (b c : Bit) : chi (b+c) = chi b * chi c := by
  fin_cases b <;> fin_cases c <;> norm_num [chi] <;> decide
@[simp] theorem chi_sq (b : Bit) : chi b * chi b = 1 := by
  rw [← chi_add, CharTwo.add_self_eq_zero, chi_zero]

@[simp] theorem dot_zero {n} (a : Word n) : dot a 0 = 0 := by simp [dot]
@[simp] theorem zero_dot {n} (a : Word n) : dot 0 a = 0 := by simp [dot]
theorem dot_comm {n} (a b : Word n) : dot a b = dot b a := by simp [dot, mul_comm]
theorem dot_add {n} (a b c : Word n) : dot a (b+c) = dot a b + dot a c := by
  simp [dot, mul_add, sum_add_distrib]
theorem add_dot {n} (a b c : Word n) : dot (a+b) c = dot a c + dot b c := by
  simp [dot, add_mul, sum_add_distrib]

@[simp] theorem word_self {n} (a : Word n) : a+a=0 := by
  funext i; exact CharTwo.add_self_eq_zero _
@[simp] theorem label_self {n} (a : Label n) : a+a=0 := Prod.ext (word_self _) (word_self _)
@[simp] theorem word_card (n : ℕ) : (Fintype.card (Word n) : ℝ) = dim n := by
  simp [dim, Fintype.card_pi]
@[simp] theorem label_card (n : ℕ) : (Fintype.card (Label n) : ℝ) = dim n ^ 2 := by
  rw [Fintype.card_prod, Nat.cast_mul, word_card, sq]

theorem sum_shift {G : Type*} [Fintype G] [AddGroup G] (g : G) (f : G → ℝ) :
    (∑ x, f (x+g)) = ∑ x, f x := Equiv.sum_comp (Equiv.addRight g) f

theorem sum_character {n} (a : Word n) :
    (∑ x, chi (dot a x)) = if a = 0 then dim n else 0 := by
  classical
  split_ifs with h
  · subst a; simp [dim]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      exact Function.ne_iff.mp h
    let e : Word n := Pi.single i 1
    have he : dot a e = a i := by simp [dot, e, Pi.single_apply]
    have ht := sum_shift e (fun x => chi (dot a x))
    simp only [dot_add, chi_add, he, ← sum_mul] at ht
    rw [show chi (a i) = -1 by simp [chi, hi]] at ht
    linarith

theorem q_add {n} (p r : Label n) : q (p+r) = q p + q r + polar p r := by
  simp only [q, polar, cross, Prod.fst_add, Prod.snd_add, add_dot, dot_add]
  rw [dot_comm p.2 r.1, dot_comm r.2 p.1]; abel

def points (n : ℕ) : Finset (Label n) := univ.filter fun p => p ≠ 0 ∧ q p = 0
@[simp] theorem mem_points {n} {p : Label n} : p ∈ points n ↔ p ≠ 0 ∧ q p = 0 := by simp [points]

/-- Column x is the image of the computational basis vector x. -/
def pauli {n} (p : Label n) : Mat n :=
  fun y x => if y = x + p.1 then chi (dot p.2 x) else 0

theorem pauli_mul {n} (p r : Label n) :
    pauli p * pauli r = chi (cross p r) • pauli (p+r) := by
  classical
  ext y x
  simp only [Matrix.mul_apply, pauli, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true,
    Matrix.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, cross, dot_add, add_dot, chi_add]
  rw [show x+r.1+p.1=x+(p.1+r.1) by abel]
  split_ifs <;> ring

theorem pauli_trace {n} (p : Label n) :
    (pauli p).trace = if p=0 then dim n else 0 := by
  classical
  rcases p with ⟨a,b⟩
  by_cases ha : a=0
  · subst a
    simpa [trace, Matrix.diag, pauli, Prod.ext_iff] using sum_character b
  · simp [trace, Matrix.diag, pauli, ha, Prod.ext_iff]

theorem pauli_hermitian {n} {p : Label n} (hp : q p = 0) :
    (pauli p).IsHermitian := by
  ext x y
  change (star (pauli p y x)) = pauli p x y
  simp only [star_trivial, pauli]
  have ht : y = x+p.1 ↔ x = y+p.1 := by
    constructor <;> rintro rfl <;> simp [add_assoc]
  by_cases h : y = x+p.1
  · rw [if_pos h, if_pos (ht.mp h), h, dot_add, dot_comm p.2 p.1, ← q, hp, add_zero]
  · rw [if_neg h, if_neg (mt ht.mpr h)]

end Quadric
