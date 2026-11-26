import ZonotopeFlips.Flips

/-!
# The total number of flips

Summing the four class sizes over all pairs `i < j` of `{0, …, n-1}` gives
`n (n + 5) 2 ^ (n - 4)`; with `n = d + 3` this is Stephan's formula
`(d² + 11 d + 24) 2 ^ (d - 1)` for OEIS A060621.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

/-! ### Block sizes for `S = {0, …, n-1}` -/

theorem nA_range {n i : ℕ} (hi : i < n) : nA (range n) i = i := by
  unfold nA
  have : (range n).filter (fun q => q < i) = range i := by
    ext q; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

theorem nB_range {n i j : ℕ} (hj : j < n) : nB (range n) i j = j - i - 1 := by
  unfold nB
  have : (range n).filter (fun q => i < q ∧ q < j) = Ioo i j := by
    ext q; simp only [mem_filter, mem_range, mem_Ioo]; omega
  rw [this, Nat.card_Ioo]

theorem nC_range {n j : ℕ} : nC (range n) j = n - j - 1 := by
  unfold nC
  have : (range n).filter (fun q => j < q) = Ioo j n := by
    ext q; simp only [mem_filter, mem_range, mem_Ioo]; omega
  rw [this, Nat.card_Ioo]

/-- The number of flips at the pair `i < j` of `{0, …, m+2}`. -/
theorem card_flipSet_range (m : ℕ) {i j : ℕ} (hij : i < j) (hjn : j < m + 3) :
    (flipSet (range (m + 3)) i j).card
      = 2 * 2 ^ ((j - i - 1 - 1) + (m + 1 - (j - i - 1) - 1))
        + 2 * Nat.choose (m + 1) (j - i - 1) := by
  have hi : i ∈ range (m + 3) := mem_range.mpr (by omega)
  have hj : j ∈ range (m + 3) := mem_range.mpr hjn
  rw [card_flipSet hi hj hij (by rw [card_range]; omega), card_UU hi hj hij, card_UD hi hj hij,
    card_DD _ _ i j rfl hi hj hij, card_DU _ _ i j rfl hi hj hij,
    nA_range (by omega), nB_range hjn, nC_range]
  have e1 : j - i - 1 - 1 + (i + (m + 3 - j - 1) - 1)
      = (j - i - 1 - 1) + (m + 1 - (j - i - 1) - 1) := by omega
  have e2 : i + (j - i - 1) + (m + 3 - j - 1) = m + 1 := by omega
  rw [e1, e2]
  ring

/-! ### Summation lemmas -/

theorem sum_pairs_range (n : ℕ) (F : ℕ → ℕ → ℕ) :
    ∑ p ∈ pairs (range n), F p.1 p.2 = ∑ j ∈ range n, ∑ i ∈ range j, F i j := by
  apply Finset.sum_finset_product_right'
  rintro ⟨i, j⟩
  simp only [mem_pairs, mem_range]
  omega

theorem sum_tri (g : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, g (j - i - 1) = ∑ β ∈ range n, (n - 1 - β) * g β := by
  have inner : ∀ j, ∑ i ∈ range j, g (j - i - 1) = ∑ β ∈ range j, g β := by
    intro j
    rw [← Finset.sum_range_reflect g j]
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    congr 1
    omega
  simp only [inner]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, ← sum_add_distrib]
    have h0 : (n + 1 - 1 - n) * g n = 0 := by
      rw [show n + 1 - 1 - n = 0 by omega, zero_mul]
    rw [h0, add_zero]
    apply sum_congr rfl
    intro β hβ
    have := mem_range.mp hβ
    rw [show n + 1 - 1 - β = (n - 1 - β) + 1 by omega]
    ring

theorem sum_add_two (m : ℕ) : 2 * ∑ β ∈ range m, (β + 2) = m * (m + 3) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ, mul_add, ih]; ring

theorem sum_two (m : ℕ) : 2 * ∑ β ∈ range m, (m + 1 - β) = m * (m + 3) := by
  have h1 : ∑ β ∈ range m, (m + 1 - β) = ∑ β ∈ range m, (β + 2) := by
    rw [← Finset.sum_range_reflect (fun β => β + 2) m]
    apply sum_congr rfl
    intro β hβ
    have := mem_range.mp hβ
    show m + 1 - β = m - 1 - β + 2
    omega
  rw [h1]
  exact sum_add_two m

/-- `∑ (m + 1 - β) C(m, β) = (m + 2) 2 ^ (m - 1)`, written without division. -/
theorem sum_T (m : ℕ) :
    2 * ∑ β ∈ range (m + 1), (m + 1 - β) * Nat.choose m β = (m + 2) * 2 ^ m := by
  have h1 : ∑ β ∈ range (m + 1), (m + 1 - β) * Nat.choose m β
      = ∑ β ∈ range (m + 1), (β + 1) * Nat.choose m β := by
    rw [← Finset.sum_range_reflect (fun β => (β + 1) * Nat.choose m β) (m + 1)]
    apply sum_congr rfl
    intro β hβ
    have hβ' : β ≤ m := by have := mem_range.mp hβ; omega
    show (m + 1 - β) * Nat.choose m β = (m + 1 - 1 - β + 1) * Nat.choose m (m + 1 - 1 - β)
    rw [show m + 1 - 1 - β = m - β by omega, Nat.choose_symm hβ',
      show m - β + 1 = m + 1 - β by omega]
  have h2 : ∑ β ∈ range (m + 1), (m + 1 - β) * Nat.choose m β
      + ∑ β ∈ range (m + 1), (β + 1) * Nat.choose m β = (m + 2) * 2 ^ m := by
    rw [← sum_add_distrib, ← Nat.sum_range_choose m, mul_sum]
    apply sum_congr rfl
    intro β hβ
    have hβ' : β ≤ m := by have := mem_range.mp hβ; omega
    rw [← add_mul]
    congr 1
    omega
  rw [← h1] at h2
  linarith

theorem final_arith (k s P : ℕ) (hg : 2 * s = (k + 1) * (k + 1 + 3)) :
    4 * (s * P + (k + 1 + 2) * (2 * P) + 2 * P + 0) = (k + 1 + 3) * (k + 1 + 4) * (2 * P) := by
  have e : 4 * (s * P + (k + 1 + 2) * (2 * P) + 2 * P + 0)
      = (2 * s) * (2 * P) + (8 * (k + 3) + 8) * P := by ring
  rw [e, hg]
  ring

/-- The sum of the `DD`-type contributions. -/
theorem sum_X (m : ℕ) :
    4 * ∑ β ∈ range (m + 3), (m + 2 - β) * 2 ^ ((β - 1) + (m + 1 - β - 1))
      = (m + 3) * (m + 4) * 2 ^ m := by
  rw [sum_range_succ, sum_range_succ, sum_range_succ']
  have hmid : ∑ k ∈ range m, (m + 2 - (k + 1)) * 2 ^ ((k + 1 - 1) + (m + 1 - (k + 1) - 1))
      = (∑ k ∈ range m, (m + 1 - k)) * 2 ^ (m - 1) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    have := mem_range.mp hk
    rw [show m + 2 - (k + 1) = m + 1 - k by omega,
      show k + 1 - 1 + (m + 1 - (k + 1) - 1) = m - 1 by omega]
  have h0 : (m + 2 - 0) * 2 ^ ((0 - 1) + (m + 1 - 0 - 1)) = (m + 2) * 2 ^ m := by
    rw [show (0 - 1) + (m + 1 - 0 - 1) = m by omega, show m + 2 - 0 = m + 2 by omega]
  have h1 : (m + 2 - (m + 1)) * 2 ^ ((m + 1 - 1) + (m + 1 - (m + 1) - 1)) = 2 ^ m := by
    rw [show m + 2 - (m + 1) = 1 by omega,
      show (m + 1 - 1) + (m + 1 - (m + 1) - 1) = m by omega, one_mul]
  have h2 : (m + 2 - (m + 2)) * 2 ^ ((m + 2 - 1) + (m + 1 - (m + 2) - 1)) = 0 := by
    rw [show m + 2 - (m + 2) = 0 by omega, zero_mul]
  rw [hmid, h0, h1, h2]
  have hg := sum_two m
  rcases m with _ | k
  · simp
  · rw [show k + 1 - 1 = k by omega, pow_succ, mul_comm (2 ^ k) 2]
    exact final_arith k _ _ hg

/-! ### The main theorem -/

/-- The number of flips between consistent graphs on `{0, …, n-1}`: pairs `(G, ij)` with
`i < j < n`, `ij ∉ G`, and both `G` and `G + ij` consistent. -/
def flipCount (n : ℕ) : ℕ := ∑ p ∈ pairs (range n), (flipSet (range n) p.1 p.2).card

/-- **Stephan's Conjecture 69 (OEIS A060621).**  The number of flips between the
`d`-dimensional tilings of the cyclic zonotope `Z(d + 3, d)` — in the consistent-graph model,
the number of flips on `d + 3` vertices — is `(d² + 11 d + 24) 2 ^ (d - 1)`. -/
theorem two_mul_flipCount (d : ℕ) :
    2 * flipCount (d + 3) = (d ^ 2 + 11 * d + 24) * 2 ^ d := by
  unfold flipCount
  have h1 : ∑ p ∈ pairs (range (d + 3)), (flipSet (range (d + 3)) p.1 p.2).card
      = ∑ p ∈ pairs (range (d + 3)),
          (fun i j => 2 * 2 ^ ((j - i - 1 - 1) + (d + 1 - (j - i - 1) - 1))
            + 2 * Nat.choose (d + 1) (j - i - 1)) p.1 p.2 := by
    apply sum_congr rfl
    rintro ⟨i, j⟩ hp
    have h := mem_pairs.mp hp
    simp only [mem_range] at h
    exact card_flipSet_range d h.2.2 h.2.1
  rw [h1, sum_pairs_range (d + 3)
      (fun i j => 2 * 2 ^ ((j - i - 1 - 1) + (d + 1 - (j - i - 1) - 1))
        + 2 * Nat.choose (d + 1) (j - i - 1)),
    sum_tri (fun β => 2 * 2 ^ ((β - 1) + (d + 1 - β - 1)) + 2 * Nat.choose (d + 1) β) (d + 3)]
  have hsplit : ∑ β ∈ range (d + 3), (d + 3 - 1 - β) *
        (2 * 2 ^ ((β - 1) + (d + 1 - β - 1)) + 2 * Nat.choose (d + 1) β)
      = 2 * ∑ β ∈ range (d + 3), (d + 2 - β) * 2 ^ ((β - 1) + (d + 1 - β - 1))
        + 2 * ∑ β ∈ range (d + 3), (d + 2 - β) * Nat.choose (d + 1) β := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro β _
    rw [show d + 3 - 1 - β = d + 2 - β by omega]
    ring
  rw [hsplit]
  have hX := sum_X d
  have hY : 2 * ∑ β ∈ range (d + 3), (d + 2 - β) * Nat.choose (d + 1) β
      = (d + 3) * 2 ^ (d + 1) := by
    rw [sum_range_succ, show d + 2 - (d + 2) = 0 by omega, zero_mul, add_zero]
    exact sum_T (d + 1)
  rw [pow_succ] at hY
  nlinarith [hX, hY]

/-- The same count in terms of the number of vertices: `n (n + 5) 2 ^ (n - 4)` for `n ≥ 4`. -/
theorem flipCount_eq (n : ℕ) (hn : 4 ≤ n) : flipCount n = n * (n + 5) * 2 ^ (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := two_mul_flipCount (k + 1)
  rw [show k + 1 + 3 = k + 4 by omega, pow_succ] at h
  rw [show k + 4 - 4 = k by omega]
  have h' : 2 * flipCount (k + 4) = 2 * ((k + 4) * (k + 4 + 5) * 2 ^ k) := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

/-- The three-vertex case: the flip graph is the 3-cube, with 12 edges. -/
theorem flipCount_three : flipCount 3 = 12 := by
  have h := two_mul_flipCount 0
  norm_num at h
  omega

/-- The first terms of OEIS A060621 (offset 0), as listed there on 2026-11-26. -/
theorem flipCount_values :
    flipCount 3 = 12 ∧ flipCount 4 = 36 ∧ flipCount 5 = 100 ∧ flipCount 6 = 264 ∧
      flipCount 7 = 672 ∧ flipCount 8 = 1664 ∧ flipCount 9 = 4032 ∧ flipCount 10 = 9600 ∧
      flipCount 11 = 22528 ∧ flipCount 12 = 52224 := by
  refine ⟨flipCount_three, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [flipCount_eq _ (by norm_num)]; norm_num)

/-! ### The set of all flips, written out -/

/-- All pairs `(G, e)`: `G` a consistent graph on `{0, …, n-1}`, `e` a pair of vertices that is
not an edge of `G`, such that `G + e` is consistent as well.  These are the edges of the flip
graph (the Hasse diagram of the higher Bruhat order `B(n, n-3)`). -/
def flipPairs (n : ℕ) : Finset (Graph × (ℕ × ℕ)) :=
  @Finset.filter _
    (fun x => Consistent (range n) x.1 ∧ x.2 ∉ x.1 ∧ Consistent (range n) (insert x.2 x.1))
    (fun _ => Classical.propDecidable _) (graphs (range n) ×ˢ pairs (range n))

theorem card_flipPairs (n : ℕ) : (flipPairs n).card = flipCount n := by
  unfold flipPairs flipCount
  rw [Finset.card_filter, Finset.sum_product_right]
  apply sum_congr rfl
  intro p _
  unfold flipSet sel
  rw [Finset.card_filter]
  rfl

/-- **Main theorem**, stated for the explicit set of flips. -/
theorem card_flipPairs_eq (d : ℕ) :
    2 * (flipPairs (d + 3)).card = (d ^ 2 + 11 * d + 24) * 2 ^ d := by
  rw [card_flipPairs]; exact two_mul_flipCount d

end

end ZonoFlips
