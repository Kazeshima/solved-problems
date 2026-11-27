/-
Two infinite families of ratio-determined insertion sequences: Layman's conjectures (C.2) and (C.4).
-/
import Insertion.Core

namespace Insertion

/-! ### Reading the process one step at a time -/

/-- The term of the sequence read off from a state. -/
theorem rdis_of_state {p q n X Y : ℕ} (h : state p q n = (X, Y)) : rdis p q n = X :=
  congrArg Prod.fst h

/-- One step of the process, on states: `next_eq` with the bookkeeping removed. -/
theorem state_succ_of {p q n X Y : ℕ} (j : ℕ) (hp : 0 < p) (hs : state p q n = (X, Y))
    (hX : 0 < X) (h1 : j = 0 ∨ p * (Y + j * X) ≤ q * X) (h2 : q * X < p * (X + Y + j * X)) :
    state p q (n + 1) = (X + Y + j * X, Y + j * X) := by
  rw [state_succ, hs]
  exact next_eq p q X Y j hp hX h1 h2

/-! ### Layman's (C.2): every step makes `m - 1 = k` further insertions -/

/-- The cone preserved by the steps of `layman_C2` (with `m = k + 1`). -/
structure Cone2 (k X Y : ℕ) : Prop where
  posX : 0 < X
  posY : 0 < Y
  le : Y ≤ X
  lt : k * X < (k + 1) * Y

theorem C2_succ {k p q n X Y : ℕ} (hp : 0 < p) (h1 : (k + 1) * p ≤ q)
    (h2 : (k + 1) * q + p ≤ ((k + 1) * (k + 1) + (k + 1)) * p)
    (hs : state p q n = (X, Y)) (hc : Cone2 k X Y) :
    state p q (n + 1) = (X + Y + k * X, Y + k * X) ∧ Cone2 k (X + Y + k * X) (Y + k * X) := by
  obtain ⟨hX, hY, hYX, hXY⟩ := hc
  have a : p * (Y + k * X) ≤ q * X := by
    have e1 : p * Y ≤ p * X := Nat.mul_le_mul_left p hYX
    have e2 : (k + 1) * p * X ≤ q * X := Nat.mul_le_mul_right X h1
    linarith [e1, e2]
  have b : q * X < p * (X + Y + k * X) := by
    have e1 : ((k + 1) * q + p) * X ≤ ((k + 1) * (k + 1) + (k + 1)) * p * X :=
      Nat.mul_le_mul_right X h2
    have e2 : p * (k * X) < p * ((k + 1) * Y) := mul_lt_mul_of_pos_left hXY hp
    have e3 : (k + 1) * (q * X) < (k + 1) * (p * (X + Y + k * X)) := by
      linarith [e1, e2]
    exact lt_of_mul_lt_mul_left e3 (Nat.zero_le _)
  refine ⟨state_succ_of k hp hs hX (Or.inr a) b, ⟨?_, ?_, ?_, ?_⟩⟩
  · omega
  · omega
  · omega
  · linarith [hY]

theorem C2_state {k p q : ℕ} (hp : 0 < p) (h1 : (k + 1) * p ≤ q)
    (h2 : (k + 1) * q + p ≤ ((k + 1) * (k + 1) + (k + 1)) * p) (n : ℕ) :
    ∃ X Y, state p q n = (X, Y) ∧ Cone2 k X Y := by
  induction n with
  | zero => exact ⟨1, 1, state_zero p q, ⟨Nat.one_pos, Nat.one_pos, le_refl 1, by omega⟩⟩
  | succ n ih =>
    obtain ⟨X, Y, hs, hc⟩ := ih
    exact ⟨_, _, C2_succ hp h1 h2 hs hc⟩

/-- **Layman's (C.2).**  For every `m ≥ 1` the sequence `I(1/m)` is `1, m + 1, ...` and satisfies
`a(n+2) = (m+1) a(n+1) - a(n)`.  The same holds for every ratio `p / q` with
`m / (m² + m - 1) ≤ p / q ≤ 1 / m`. -/
theorem layman_C2 (m p q : ℕ) (hm : 0 < m) (hp : 0 < p) (h1 : m * p ≤ q)
    (h2 : m * q + p ≤ (m * m + m) * p) :
    rdis p q 0 = 1 ∧ rdis p q 1 = m + 1 ∧
      ∀ n, rdis p q (n + 2) + rdis p q n = (m + 1) * rdis p q (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hc0 : Cone2 k 1 1 := ⟨Nat.one_pos, Nat.one_pos, le_refl 1, by omega⟩
  refine ⟨rfl, ?_, ?_⟩
  · obtain ⟨hs1, -⟩ := C2_succ hp h1 h2 (state_zero p q) hc0
    have e : rdis p q 1 = _ := rdis_of_state hs1
    rw [e]
    ring
  · intro n
    obtain ⟨X, Y, hs, hc⟩ := C2_state hp h1 h2 n
    obtain ⟨hs1, hc1⟩ := C2_succ hp h1 h2 hs hc
    obtain ⟨hs2, -⟩ := C2_succ hp h1 h2 hs1 hc1
    have e0 : rdis p q n = _ := rdis_of_state hs
    have e1 : rdis p q (n + 1) = _ := rdis_of_state hs1
    have e2 : rdis p q (n + 2) = _ := rdis_of_state hs2
    rw [e0, e1, e2]
    ring

/-! ### The twin of (C.2): first `m - 2 = k` further insertions, then always `m - 1 = k + 1` -/

/-- The cone preserved by the later steps of `layman_C2_twin` (with `m = k + 2`). -/
structure ConeT (k X Y : ℕ) : Prop where
  posX : 0 < X
  posY : 0 < Y
  le : Y ≤ X
  lt : (k + 3) * Y ≤ (k + 2) * X

theorem twin_first {k p q : ℕ} (hp : 0 < p) (h1 : q < (k + 2) * p)
    (h2 : ((k + 2) * (k + 2) + (k + 2)) * p ≤ (k + 2 + 1) * q + p) :
    state p q 1 = (k + 2, k + 1) := by
  have a : p * (1 + k * 1) ≤ q * 1 := by
    have a' : (k + 3) * (p * (1 + k * 1)) ≤ (k + 3) * (q * 1) := by
      linarith [h2, Nat.zero_le (k * p)]
    exact le_of_mul_le_mul_left a' (by omega)
  have b : q * 1 < p * (1 + 1 + k * 1) := by
    linarith [h1]
  have e : state p q (0 + 1) = (1 + 1 + k * 1, 1 + k * 1) :=
    state_succ_of k hp (state_zero p q) Nat.one_pos (Or.inr a) b
  have e1 : 1 + 1 + k * 1 = k + 2 := by omega
  have e2 : 1 + k * 1 = k + 1 := by omega
  rw [e1, e2] at e
  exact e

theorem twin_cone (k : ℕ) : ConeT k (k + 2) (k + 1) :=
  ⟨by omega, by omega, by omega, by linarith [Nat.zero_le (k * k)]⟩

theorem twin_succ {k p q n X Y : ℕ} (hp : 0 < p) (h1 : q < (k + 2) * p)
    (h2 : ((k + 2) * (k + 2) + (k + 2)) * p ≤ (k + 2 + 1) * q + p)
    (hs : state p q n = (X, Y)) (hc : ConeT k X Y) :
    state p q (n + 1) = (X + Y + (k + 1) * X, Y + (k + 1) * X) ∧
      ConeT k (X + Y + (k + 1) * X) (Y + (k + 1) * X) := by
  obtain ⟨hX, hY, hYX, hXY⟩ := hc
  have a : p * (Y + (k + 1) * X) ≤ q * X := by
    have e1 : ((k + 2) * (k + 2) + (k + 2)) * p * X ≤ ((k + 2 + 1) * q + p) * X :=
      Nat.mul_le_mul_right X h2
    have e2 : p * ((k + 3) * Y) ≤ p * ((k + 2) * X) := Nat.mul_le_mul_left p hXY
    have e3 : (k + 3) * (p * (Y + (k + 1) * X)) ≤ (k + 3) * (q * X) := by
      linarith [e1, e2]
    exact le_of_mul_le_mul_left e3 (by omega)
  have b : q * X < p * (X + Y + (k + 1) * X) := by
    have e1 : q * X < (k + 2) * p * X := mul_lt_mul_of_pos_right h1 hX
    linarith [e1, Nat.zero_le (p * Y)]
  refine ⟨state_succ_of (k + 1) hp hs hX (Or.inr a) b, ⟨?_, ?_, ?_, ?_⟩⟩
  · omega
  · omega
  · omega
  · linarith [hYX]

theorem twin_state {k p q : ℕ} (hp : 0 < p) (h1 : q < (k + 2) * p)
    (h2 : ((k + 2) * (k + 2) + (k + 2)) * p ≤ (k + 2 + 1) * q + p) (n : ℕ) :
    ∃ X Y, state p q (n + 1) = (X, Y) ∧ ConeT k X Y := by
  induction n with
  | zero => exact ⟨k + 2, k + 1, twin_first hp h1 h2, twin_cone k⟩
  | succ n ih =>
    obtain ⟨X, Y, hs, hc⟩ := ih
    exact ⟨_, _, twin_succ hp h1 h2 hs hc⟩

/-- The twin of `I(1/m)`: for `1 / m < p / q ≤ (m + 1) / (m² + m - 1)` the sequence is
`1, m, ...` and satisfies the same recurrence `a(n+2) = (m+1) a(n+1) - a(n)`. -/
theorem layman_C2_twin (m p q : ℕ) (hm : 2 ≤ m) (hp : 0 < p) (h1 : q < m * p)
    (h2 : (m * m + m) * p ≤ (m + 1) * q + p) :
    rdis p q 0 = 1 ∧ rdis p q 1 = m ∧
      ∀ n, rdis p q (n + 2) + rdis p q n = (m + 1) * rdis p q (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hs1 : state p q 1 = (k + 2, k + 1) := twin_first hp h1 h2
  refine ⟨rfl, rdis_of_state hs1, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨hs2, -⟩ := twin_succ hp h1 h2 hs1 (twin_cone k)
    have e0 : rdis p q 0 = 1 := rfl
    have e1 : rdis p q 1 = k + 2 := rdis_of_state hs1
    have e2 : rdis p q 2 = _ := rdis_of_state hs2
    have key : rdis p q 2 + rdis p q 0 = (k + 2 + 1) * rdis p q 1 := by
      rw [e0, e1, e2]
      ring
    exact key
  · obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    obtain ⟨X, Y, hs, hc⟩ := twin_state hp h1 h2 i
    obtain ⟨t1, hc1⟩ := twin_succ hp h1 h2 hs hc
    obtain ⟨t2, -⟩ := twin_succ hp h1 h2 t1 hc1
    have e0 : rdis p q (i + 1) = _ := rdis_of_state hs
    have e1 : rdis p q (i + 1 + 1) = _ := rdis_of_state t1
    have e2 : rdis p q (i + 1 + 2) = _ := rdis_of_state t2
    rw [e0, e1, e2]
    ring

/-! ### Layman's (C.4): the steps alternate `m - 2 = k` and `m - 1 = k + 1` further insertions -/

/-- The cone of the even-numbered states of `layman_C4` (with `m = k + 2`). -/
structure ConeE (k X Y : ℕ) : Prop where
  posX : 0 < X
  posY : 0 < Y
  le : Y ≤ X
  lt : (k + 1) * X < (k + 2) * Y

/-- The cone of the odd-numbered states of `layman_C4` (with `m = k + 2`). -/
structure ConeO (k X Y : ℕ) : Prop where
  posX : 0 < X
  posY : 0 < Y
  le : (k + 2) * Y ≤ (k + 1) * X

theorem C4_even_succ {k q n X Y : ℕ} (hq : q + 1 = (k + 2) * (k + 2))
    (hs : state (k + 2) q n = (X, Y)) (hc : ConeE k X Y) :
    state (k + 2) q (n + 1) = (X + Y + k * X, Y + k * X) ∧
      ConeO k (X + Y + k * X) (Y + k * X) := by
  obtain ⟨hX, hY, hYX, hXY⟩ := hc
  have hqX : (q + 1) * X = (k + 2) * (k + 2) * X := by rw [hq]
  have a : (k + 2) * (Y + k * X) ≤ q * X := by
    linarith [hqX, Nat.mul_le_mul_left (k + 2) hYX, Nat.zero_le (k * X)]
  have b : q * X < (k + 2) * (X + Y + k * X) := by
    linarith [hqX, hXY]
  refine ⟨state_succ_of k (by omega) hs hX (Or.inr a) b, ⟨?_, ?_, ?_⟩⟩
  · omega
  · omega
  · linarith [hYX]

theorem C4_odd_succ {k q n X Y : ℕ} (hq : q + 1 = (k + 2) * (k + 2))
    (hs : state (k + 2) q n = (X, Y)) (hc : ConeO k X Y) :
    state (k + 2) q (n + 1) = (X + Y + (k + 1) * X, Y + (k + 1) * X) ∧
      ConeE k (X + Y + (k + 1) * X) (Y + (k + 1) * X) := by
  obtain ⟨hX, hY, hXY⟩ := hc
  have hqX : (q + 1) * X = (k + 2) * (k + 2) * X := by rw [hq]
  have a : (k + 2) * (Y + (k + 1) * X) ≤ q * X := by
    linarith [hqX, hXY]
  have b : q * X < (k + 2) * (X + Y + (k + 1) * X) := by
    linarith [hqX, hX, Nat.zero_le (k * Y)]
  refine ⟨state_succ_of (k + 1) (by omega) hs hX (Or.inr a) b, ⟨?_, ?_, ?_, ?_⟩⟩
  · omega
  · omega
  · omega
  · linarith [hY]

theorem C4_even_state {k q : ℕ} (hq : q + 1 = (k + 2) * (k + 2)) (i : ℕ) :
    ∃ X Y, state (k + 2) q (2 * i) = (X, Y) ∧ ConeE k X Y := by
  induction i with
  | zero =>
    exact ⟨1, 1, state_zero (k + 2) q, ⟨Nat.one_pos, Nat.one_pos, le_refl 1, by omega⟩⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, hE⟩ := ih
    obtain ⟨hs1, hO⟩ := C4_even_succ hq hs hE
    obtain ⟨hs2, hE2⟩ := C4_odd_succ hq hs1 hO
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [e]
    exact ⟨_, _, hs2, hE2⟩

/-- **Layman's (C.4).**  For every `m ≥ 2` the ratio `m / (m² - 1)`, which lies strictly between
`1 / m` and `1 / (m - 1)`, gives a sequence with `a(n+4) = (m(m+1) - 2) a(n+2) - a(n)`.
Here `q = m² - 1`. -/
theorem layman_C4 (m q : ℕ) (hm : 2 ≤ m) (hq : q + 1 = m * m) :
    (rdis m q 0 = 1 ∧ rdis m q 1 = m ∧ rdis m q 2 + 1 = m * m + m ∧
        rdis m q 3 + 2 * m = m * m * m + m * m) ∧
      ∀ n, rdis m q (n + 4) + rdis m q n + 2 * rdis m q (n + 2) =
        (m * m + m) * rdis m q (n + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hE0 : ConeE k 1 1 := ⟨Nat.one_pos, Nat.one_pos, le_refl 1, by omega⟩
  obtain ⟨hs1, hO1⟩ := C4_even_succ hq (state_zero (k + 2) q) hE0
  obtain ⟨hs2, hE2⟩ := C4_odd_succ hq hs1 hO1
  obtain ⟨hs3, -⟩ := C4_even_succ hq hs2 hE2
  have e1 : rdis (k + 2) q 1 = _ := rdis_of_state hs1
  have e2 : rdis (k + 2) q 2 = _ := rdis_of_state hs2
  have e3 : rdis (k + 2) q 3 = _ := rdis_of_state hs3
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [e1]
    ring
  · rw [e2]
    ring
  · rw [e3]
    ring
  · intro n
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨X, Y, hs, hE⟩ := C4_even_state hq i
      obtain ⟨t1, hO⟩ := C4_even_succ hq hs hE
      obtain ⟨t2, hE'⟩ := C4_odd_succ hq t1 hO
      obtain ⟨t3, hO'⟩ := C4_even_succ hq t2 hE'
      obtain ⟨t4, -⟩ := C4_odd_succ hq t3 hO'
      have f0 : rdis (k + 2) q (2 * i) = _ := rdis_of_state hs
      have f2 : rdis (k + 2) q (2 * i + 2) = _ := rdis_of_state t2
      have f4 : rdis (k + 2) q (2 * i + 4) = _ := rdis_of_state t4
      rw [f0, f2, f4]
      ring
    · obtain ⟨X, Y, hs, hE⟩ := C4_even_state hq i
      obtain ⟨t1, hO⟩ := C4_even_succ hq hs hE
      obtain ⟨t2, hE'⟩ := C4_odd_succ hq t1 hO
      obtain ⟨t3, hO'⟩ := C4_even_succ hq t2 hE'
      obtain ⟨t4, hE''⟩ := C4_odd_succ hq t3 hO'
      obtain ⟨t5, -⟩ := C4_even_succ hq t4 hE''
      have f0 : rdis (k + 2) q (2 * i + 1) = _ := rdis_of_state t1
      have f2 : rdis (k + 2) q (2 * i + 1 + 2) = _ := rdis_of_state t3
      have f4 : rdis (k + 2) q (2 * i + 1 + 4) = _ := rdis_of_state t5
      rw [f0, f2, f4]
      ring

/-- The ratio in `layman_C4` lies strictly between `1 / m` and `1 / (m - 1)`. -/
theorem layman_C4_between (m q : ℕ) (hm : 2 ≤ m) (hq : q + 1 = m * m) :
    q < m * m ∧ (m - 1) * m < q := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e : k + 2 - 1 = k + 1 := by omega
  rw [e]
  constructor
  · omega
  · linarith [hq, Nat.zero_le (k * k)]

end Insertion
