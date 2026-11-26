/-
Lattice points of `ℤ^d` in a ball: congruences modulo powers of two.

OEIS A055414 counts the points of `ℤ^8` of Euclidean norm at most `n`.
Ralf Stephan observed on 7 July 2003 that "numbers so far are all 1 mod 16".
This file proves the observation for every radius, and more generally that the
number of points of `ℤ^(2^k)` in any ball centred at the origin is congruent to
`1` modulo `2^(k+1)`.

Proof.  Write `N d R` for the number of `x : ℤ^d` with `∑ xᵢ² ≤ R`.
* Splitting the coordinates gives `N (d+d) R = ∑_{u, |u|² ≤ R} N d (R - |u|²)`.
* If `N d · ≡ 1 (mod M)` for every radius, each summand is `1 + (multiple of M)`.
  The nonzero `u` come in pairs `u, -u` with equal summands, so the multiples of
  `M` add up to a multiple of `2M`.  Hence
  `N (d+d) R ≡ N d R + (N d R - 1) ≡ 1 (mod 2M)`.
* The same pairing shows that `N d R` is odd, which starts the induction.
-/
import Mathlib

open Finset

namespace LatticeBall

/-- Points of `ℤ^d` whose squared Euclidean norm is at most `R`.  The coordinate box
`[-R, R]` only serves to make the set visibly finite; see `mem_ballPoints`. -/
def ballPoints (d : ℕ) (R : ℤ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-R) R).filter fun x => ∑ i, x i ^ 2 ≤ R

theorem int_le_sq (a : ℤ) : a ≤ a ^ 2 := by
  rcases le_or_lt a 0 with h | h
  · exact le_trans h (sq_nonneg a)
  · have h1 : 1 ≤ a := h
    nlinarith

/-- `ballPoints d R` is exactly the set of integer points with `∑ xᵢ² ≤ R`. -/
theorem mem_ballPoints {d : ℕ} {R : ℤ} {x : Fin d → ℤ} :
    x ∈ ballPoints d R ↔ ∑ i, x i ^ 2 ≤ R := by
  unfold ballPoints
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have h1 : x i ≤ x i ^ 2 := int_le_sq (x i)
    have h2 : -(x i) ≤ x i ^ 2 := by
      have := int_le_sq (-(x i))
      rwa [neg_sq] at this
    rw [Finset.mem_Icc]
    constructor <;> linarith

theorem zero_mem_ballPoints {d : ℕ} {R : ℤ} (h : 0 ≤ R) : (0 : Fin d → ℤ) ∈ ballPoints d R := by
  rw [mem_ballPoints]
  simpa using h

theorem neg_mem_ballPoints {d : ℕ} {R : ℤ} {u : Fin d → ℤ} (h : u ∈ ballPoints d R) :
    -u ∈ ballPoints d R := by
  rw [mem_ballPoints] at h ⊢
  simpa using h

theorem neg_ne_self {d : ℕ} {u : Fin d → ℤ} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

/-- Splitting the `d + d` coordinates into two blocks of `d`. -/
theorem card_ballPoints_add (d : ℕ) (R : ℤ) :
    (ballPoints (d + d) R).card =
      ∑ u ∈ ballPoints d R, (ballPoints d (R - ∑ i, u i ^ 2)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij'
    (fun x _ => (⟨fun i => x (Fin.castAdd d i), fun i => x (Fin.natAdd d i)⟩ :
      Σ _ : Fin d → ℤ, Fin d → ℤ))
    (fun p _ => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_ballPoints, Fin.sum_univ_add] at hx
    rw [Finset.mem_sigma, mem_ballPoints, mem_ballPoints]
    have h1 : 0 ≤ ∑ i : Fin d, x (Fin.natAdd d i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    constructor <;> linarith
  · intro p hp
    rw [Finset.mem_sigma, mem_ballPoints, mem_ballPoints] at hp
    rw [mem_ballPoints, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    linarith [hp.2]
  · intro x _
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  · intro p _
    rcases p with ⟨u, v⟩
    simp only [Fin.append_left, Fin.append_right]

/-- `Inv d M`: every ball of `ℤ^d` centred at the origin has `≡ 1 (mod M)` lattice points. -/
def Inv (d M : ℕ) : Prop :=
  ∀ R : ℤ, 0 ≤ R → (M : ℤ) ∣ ((ballPoints d R).card : ℤ) - 1

theorem dvd_sub_one_of_zmod {M : ℕ} [NeZero M] {c : ℕ} (h : (c : ZMod M) = 1) :
    (M : ℤ) ∣ (c : ℤ) - 1 := by
  have h' : (((c : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    push_cast
    rw [h, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'

theorem two_mul_cast_sub_one {M : ℕ} {c : ℕ} (h : (M : ℤ) ∣ (c : ℤ) - 1) :
    (2 : ZMod (2 * M)) * ((c : ZMod (2 * M)) - 1) = 0 := by
  obtain ⟨t, ht⟩ := h
  have e : ((c : ZMod (2 * M)) - 1) = (M : ZMod (2 * M)) * (t : ZMod (2 * M)) := by
    have := congrArg (fun z : ℤ => (z : ZMod (2 * M))) ht
    push_cast at this
    exact this
  have h2 : (2 : ZMod (2 * M)) * (M : ZMod (2 * M)) = 0 := by
    have := ZMod.natCast_self (2 * M)
    push_cast at this
    exact this
  rw [e, ← mul_assoc, h2, zero_mul]

/-- Every ball centred at the origin contains an odd number of lattice points. -/
theorem inv_two (d : ℕ) : Inv d 2 := by
  intro R hR
  have h0 := zero_mem_ballPoints (d := d) hR
  apply dvd_sub_one_of_zmod
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.add_sum_erase _ _ h0]
  have hinv : ∑ u ∈ (ballPoints d R).erase 0, ((1 : ℕ) : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun u _ => -u) ?_ ?_ ?_ ?_
    · intro u _
      decide
    · intro u hu _
      exact neg_ne_self (Finset.ne_of_mem_erase hu)
    · intro u hu
      exact Finset.mem_erase.mpr
        ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hu), neg_mem_ballPoints (Finset.mem_of_mem_erase hu)⟩
    · intro u _
      simp
  rw [hinv]
  simp

/-- Doubling the dimension doubles the modulus. -/
theorem inv_double {d M : ℕ} (hM : 0 < M) (h : Inv d M) : Inv (d + d) (2 * M) := by
  intro R hR
  haveI : NeZero (2 * M) := ⟨by omega⟩
  have h0 := zero_mem_ballPoints (d := d) hR
  apply dvd_sub_one_of_zmod
  rw [card_ballPoints_add, Nat.cast_sum]
  have hterm : ∀ u ∈ ballPoints d R,
      (2 : ZMod (2 * M)) * (((ballPoints d (R - ∑ i, u i ^ 2)).card : ZMod (2 * M)) - 1) = 0 := by
    intro u hu
    apply two_mul_cast_sub_one
    apply h
    have := mem_ballPoints.mp hu
    linarith
  have hsplit : ∑ u ∈ ballPoints d R, ((ballPoints d (R - ∑ i, u i ^ 2)).card : ZMod (2 * M))
      = ∑ u ∈ ballPoints d R, (((ballPoints d (R - ∑ i, u i ^ 2)).card : ZMod (2 * M)) - 1)
        + ((ballPoints d R).card : ZMod (2 * M)) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsplit, ← Finset.add_sum_erase _ _ h0]
  have hinv : ∑ u ∈ (ballPoints d R).erase 0,
      (((ballPoints d (R - ∑ i, u i ^ 2)).card : ZMod (2 * M)) - 1) = 0 := by
    refine Finset.sum_involution (fun u _ => -u) ?_ ?_ ?_ ?_
    · intro u hu
      have e : (∑ i, (-u) i ^ 2) = ∑ i, u i ^ 2 := by simp
      rw [e]
      have h2 := hterm u (Finset.mem_of_mem_erase hu)
      linear_combination h2
    · intro u hu _
      exact neg_ne_self (Finset.ne_of_mem_erase hu)
    · intro u hu
      exact Finset.mem_erase.mpr
        ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hu), neg_mem_ballPoints (Finset.mem_of_mem_erase hu)⟩
    · intro u _
      simp
  rw [hinv, add_zero]
  have hz := hterm 0 h0
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, sub_zero] at hz ⊢
  linear_combination hz

/-- In dimension `2^k` the number of lattice points in a ball is `≡ 1 (mod 2^(k+1))`. -/
theorem inv_two_pow (k : ℕ) : Inv (2 ^ k) (2 ^ (k + 1)) := by
  induction k with
  | zero => simpa using inv_two 1
  | succ k ih =>
    have h := inv_double (by positivity) ih
    have e1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have e2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [e1, e2]
    exact h

/-- Any ball of `ℤ^8` centred at the origin contains `≡ 1 (mod 16)` lattice points. -/
theorem inv_eight : Inv 8 16 := inv_two_pow 3

theorem inv_four : Inv 4 8 := inv_two_pow 2

theorem card_ballPoints_eight_mod (R : ℤ) (hR : 0 ≤ R) : (ballPoints 8 R).card % 16 = 1 := by
  obtain ⟨t, ht⟩ := inv_eight R hR
  push_cast at ht
  omega

/-- **Stephan's 2003 observation for OEIS A055414.**  The number of points of `ℤ^8` of
norm at most `n` is congruent to `1` modulo `16`, for every `n`. -/
theorem A055414_mod_sixteen (n : ℕ) : (ballPoints 8 ((n : ℤ) ^ 2)).card % 16 = 1 :=
  card_ballPoints_eight_mod _ (sq_nonneg _)

/-- The same statement for the sibling sequence A055410 (`ℤ^4`, modulus `8`). -/
theorem A055410_mod_eight (n : ℕ) : (ballPoints 4 ((n : ℤ) ^ 2)).card % 8 = 1 := by
  obtain ⟨t, ht⟩ := inv_four ((n : ℤ) ^ 2) (sq_nonneg _)
  push_cast at ht
  omega

/-! Sanity checks against the OEIS data (evaluated, not part of any proof):
A055414(1) = 17, A055410(2) = 89, and the 81 lattice points in the disc of radius 5. -/
#guard (ballPoints 8 1).card == 17
#guard (ballPoints 4 4).card == 89
#guard (ballPoints 2 25).card == 81

end LatticeBall
