/-
The six ratio-determined insertion sequences in the OEIS whose recurrences were conjectured in
2003-2004: A082630, A082981, A085260, A085376, A085348, A085349.

Positions are counted from `0` here; the OEIS entries count from `1` (A085348 from `0`).

Method.  For each sequence the numbers `j` of further insertions are periodic.  The states at the
start of a period stay in a cone, cut out by two linear inequalities, on which the whole period is
forced; this is proved by induction (`*_base`).  From a period-start state `(X, Y)` the next
states are explicit linear forms in `X, Y` (`*_window`), so the recurrences are linear identities
and the product identities follow from a quadratic invariant of the period-start states.
-/
import Insertion.Core

namespace Insertion

/-! ### Auxiliary lemmas -/

/-- One step of the process from a known state, with the number `j` of further insertions and the
new state `(X', Y')` given explicitly.  For numerals `p, q, j` and linear forms `X, Y, X', Y'` the
side condition is a linear statement. -/
theorem state_step (p q n X Y j X' Y' : ℕ) (hs : state p q n = (X, Y))
    (h : 0 < p ∧ 0 < X ∧ (j = 0 ∨ p * (Y + j * X) ≤ q * X) ∧ q * X < p * (X + Y + j * X) ∧
      X' = X + Y + j * X ∧ Y' = Y + j * X) :
    state p q (n + 1) = (X', Y') := by
  obtain ⟨hp, hX, h1, h2, rfl, rfl⟩ := h
  rw [state_succ, hs]
  exact next_eq p q X Y j hp hX h1 h2

theorem rdis_of_state {p q n X Y : ℕ} (h : state p q n = (X, Y)) : rdis p q n = X := by
  rw [rdis, h]

/-! ### A082630: insert when `7 b ≤ 11 a` -/

/-- The states with even index stay in the cone `4 X < 7 Y`, `3 Y ≤ 4 X`, where the pattern
`j = 0, 1` is forced, and satisfy `X² + 2 = 3 Y²`; both coordinates are odd. -/
theorem A082630_base (i : ℕ) :
    ∃ X Y, state 7 11 (2 * i) = (X, Y) ∧ 4 * X < 7 * Y ∧ 3 * Y ≤ 4 * X ∧
      X ^ 2 + 2 = 3 * Y ^ 2 ∧ X % 2 = 1 ∧ Y % 2 = 1 := by
  induction i with
  | zero => exact ⟨1, 1, state_zero 7 11, by norm_num, by norm_num, by norm_num, rfl, rfl⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, h1, h2, hq, hX, hY⟩ := ih
    have s1 : state 7 11 (2 * i + 1) = (X + Y, Y) :=
      state_step 7 11 (2 * i) _ _ 0 _ _ hs (by omega)
    have s2 : state 7 11 (2 * i + 2) = (2 * X + 3 * Y, X + 2 * Y) :=
      state_step 7 11 (2 * i + 1) _ _ 1 _ _ s1 (by omega)
    refine ⟨2 * X + 3 * Y, X + 2 * Y, ?_, by omega, by omega, by nlinarith [hq], by omega,
      by omega⟩
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    exact s2

theorem A082630_window (i : ℕ) :
    ∃ X Y, X ^ 2 + 2 = 3 * Y ^ 2 ∧ X % 2 = 1 ∧ Y % 2 = 1 ∧
      rdis 7 11 (2 * i) = X ∧ rdis 7 11 (2 * i + 1) = X + Y ∧
      rdis 7 11 (2 * i + 2) = 2 * X + 3 * Y ∧ rdis 7 11 (2 * i + 3) = 3 * X + 5 * Y ∧
      rdis 7 11 (2 * i + 4) = 7 * X + 12 * Y ∧ rdis 7 11 (2 * i + 5) = 11 * X + 19 * Y := by
  obtain ⟨X, Y, hs, h1, h2, hq, hX, hY⟩ := A082630_base i
  have s1 : state 7 11 (2 * i + 1) = (X + Y, Y) :=
    state_step 7 11 (2 * i) _ _ 0 _ _ hs (by omega)
  have s2 : state 7 11 (2 * i + 2) = (2 * X + 3 * Y, X + 2 * Y) :=
    state_step 7 11 (2 * i + 1) _ _ 1 _ _ s1 (by omega)
  have s3 : state 7 11 (2 * i + 3) = (3 * X + 5 * Y, X + 2 * Y) :=
    state_step 7 11 (2 * i + 2) _ _ 0 _ _ s2 (by omega)
  have s4 : state 7 11 (2 * i + 4) = (7 * X + 12 * Y, 4 * X + 7 * Y) :=
    state_step 7 11 (2 * i + 3) _ _ 1 _ _ s3 (by omega)
  have s5 : state 7 11 (2 * i + 5) = (11 * X + 19 * Y, 4 * X + 7 * Y) :=
    state_step 7 11 (2 * i + 4) _ _ 0 _ _ s4 (by omega)
  exact ⟨X, Y, hq, hX, hY, rdis_of_state hs, rdis_of_state s1, rdis_of_state s2,
    rdis_of_state s3, rdis_of_state s4, rdis_of_state s5⟩

theorem A082630_values :
    rdis 7 11 0 = 1 ∧ rdis 7 11 1 = 2 ∧ rdis 7 11 2 = 5 ∧ rdis 7 11 3 = 8 := by
  decide

/-- Layman (2003): `a(n) = 4 a(n-2) - a(n-4)`. -/
theorem A082630_rec (n : ℕ) : rdis 7 11 (n + 4) + rdis 7 11 n = 4 * rdis 7 11 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, -, -, -, r0, -, r2, -, r4, -⟩ := A082630_window i
    rw [r0, r2, r4]
    omega
  · obtain ⟨X, Y, -, -, -, -, r1, -, r3, -, r5⟩ := A082630_window i
    show rdis 7 11 (2 * i + 5) + rdis 7 11 (2 * i + 1) = 4 * rdis 7 11 (2 * i + 3)
    rw [r1, r3, r5]
    omega

/-- Stephan (2004): `a(n) a(n+3) = -2 + a(n+1) a(n+2)`. -/
theorem A082630_prod (n : ℕ) :
    rdis 7 11 n * rdis 7 11 (n + 3) + 2 = rdis 7 11 (n + 1) * rdis 7 11 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, hq, -, -, r0, r1, r2, r3, -⟩ := A082630_window i
    rw [r0, r1, r2, r3]
    nlinarith [hq]
  · obtain ⟨X, Y, hq, -, -, -, r1, r2, r3, r4, -⟩ := A082630_window i
    show rdis 7 11 (2 * i + 1) * rdis 7 11 (2 * i + 4) + 2 =
      rdis 7 11 (2 * i + 2) * rdis 7 11 (2 * i + 3)
    rw [r1, r2, r3, r4]
    nlinarith [hq]

/-- Layman (2003): for the terms `1, 5, 19, 71, ...` the number `3 a² + 6` is a square. -/
theorem A082630_square_even (n : ℕ) : ∃ y, 3 * rdis 7 11 (2 * n) ^ 2 + 6 = y ^ 2 := by
  obtain ⟨X, Y, hq, -, -, r0, -⟩ := A082630_window n
  refine ⟨3 * Y, ?_⟩
  rw [r0]
  nlinarith [hq]

/-- Layman (2003): for the halves `1, 4, 15, 56, ...` of the terms `2, 8, 30, 112, ...` the number
`3 x² + 1` is a square. -/
theorem A082630_square_odd (n : ℕ) :
    ∃ x y, rdis 7 11 (2 * n + 1) = 2 * x ∧ 3 * x ^ 2 + 1 = y ^ 2 := by
  obtain ⟨X, Y, hq, hX, hY, -, r1, -⟩ := A082630_window n
  obtain ⟨a, rfl⟩ : ∃ a, X = 2 * a + 1 := ⟨X / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, Y = 2 * b + 1 := ⟨Y / 2, by omega⟩
  refine ⟨a + b + 1, a + 3 * b + 2, ?_, ?_⟩
  · rw [r1]
    omega
  · nlinarith [hq]

/-! ### A082981: insert when `4 b ≤ 5 a` -/

/-- The states with index `4 i` stay in the cone `Y ≤ X < 2 Y`, where the pattern
`j = 0, 0, 0, 1` is forced. -/
theorem A082981_base (i : ℕ) :
    ∃ X Y, state 4 5 (4 * i) = (X, Y) ∧ Y ≤ X ∧ X < 2 * Y := by
  induction i with
  | zero => exact ⟨1, 1, state_zero 4 5, by norm_num, by norm_num⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, h1, h2⟩ := ih
    have s1 : state 4 5 (4 * i + 1) = (X + Y, Y) :=
      state_step 4 5 (4 * i) _ _ 0 _ _ hs (by omega)
    have s2 : state 4 5 (4 * i + 2) = (X + 2 * Y, Y) :=
      state_step 4 5 (4 * i + 1) _ _ 0 _ _ s1 (by omega)
    have s3 : state 4 5 (4 * i + 3) = (X + 3 * Y, Y) :=
      state_step 4 5 (4 * i + 2) _ _ 0 _ _ s2 (by omega)
    have s4 : state 4 5 (4 * i + 4) = (2 * X + 7 * Y, X + 4 * Y) :=
      state_step 4 5 (4 * i + 3) _ _ 1 _ _ s3 (by omega)
    refine ⟨2 * X + 7 * Y, X + 4 * Y, ?_, by omega, by omega⟩
    rw [show 4 * (i + 1) = 4 * i + 4 by ring]
    exact s4

theorem A082981_window (i : ℕ) :
    ∃ X Y, rdis 4 5 (4 * i) = X ∧ rdis 4 5 (4 * i + 1) = X + Y ∧
      rdis 4 5 (4 * i + 2) = X + 2 * Y ∧ rdis 4 5 (4 * i + 3) = X + 3 * Y ∧
      rdis 4 5 (4 * i + 4) = 2 * X + 7 * Y ∧ rdis 4 5 (4 * i + 5) = 3 * X + 11 * Y ∧
      rdis 4 5 (4 * i + 6) = 4 * X + 15 * Y ∧ rdis 4 5 (4 * i + 7) = 5 * X + 19 * Y ∧
      rdis 4 5 (4 * i + 8) = 11 * X + 42 * Y ∧ rdis 4 5 (4 * i + 9) = 17 * X + 65 * Y ∧
      rdis 4 5 (4 * i + 10) = 23 * X + 88 * Y ∧ rdis 4 5 (4 * i + 11) = 29 * X + 111 * Y := by
  obtain ⟨X, Y, hs, h1, h2⟩ := A082981_base i
  have s1 : state 4 5 (4 * i + 1) = (X + Y, Y) :=
    state_step 4 5 (4 * i) _ _ 0 _ _ hs (by omega)
  have s2 : state 4 5 (4 * i + 2) = (X + 2 * Y, Y) :=
    state_step 4 5 (4 * i + 1) _ _ 0 _ _ s1 (by omega)
  have s3 : state 4 5 (4 * i + 3) = (X + 3 * Y, Y) :=
    state_step 4 5 (4 * i + 2) _ _ 0 _ _ s2 (by omega)
  have s4 : state 4 5 (4 * i + 4) = (2 * X + 7 * Y, X + 4 * Y) :=
    state_step 4 5 (4 * i + 3) _ _ 1 _ _ s3 (by omega)
  have s5 : state 4 5 (4 * i + 5) = (3 * X + 11 * Y, X + 4 * Y) :=
    state_step 4 5 (4 * i + 4) _ _ 0 _ _ s4 (by omega)
  have s6 : state 4 5 (4 * i + 6) = (4 * X + 15 * Y, X + 4 * Y) :=
    state_step 4 5 (4 * i + 5) _ _ 0 _ _ s5 (by omega)
  have s7 : state 4 5 (4 * i + 7) = (5 * X + 19 * Y, X + 4 * Y) :=
    state_step 4 5 (4 * i + 6) _ _ 0 _ _ s6 (by omega)
  have s8 : state 4 5 (4 * i + 8) = (11 * X + 42 * Y, 6 * X + 23 * Y) :=
    state_step 4 5 (4 * i + 7) _ _ 1 _ _ s7 (by omega)
  have s9 : state 4 5 (4 * i + 9) = (17 * X + 65 * Y, 6 * X + 23 * Y) :=
    state_step 4 5 (4 * i + 8) _ _ 0 _ _ s8 (by omega)
  have s10 : state 4 5 (4 * i + 10) = (23 * X + 88 * Y, 6 * X + 23 * Y) :=
    state_step 4 5 (4 * i + 9) _ _ 0 _ _ s9 (by omega)
  have s11 : state 4 5 (4 * i + 11) = (29 * X + 111 * Y, 6 * X + 23 * Y) :=
    state_step 4 5 (4 * i + 10) _ _ 0 _ _ s10 (by omega)
  exact ⟨X, Y, rdis_of_state hs, rdis_of_state s1, rdis_of_state s2, rdis_of_state s3,
    rdis_of_state s4, rdis_of_state s5, rdis_of_state s6, rdis_of_state s7, rdis_of_state s8,
    rdis_of_state s9, rdis_of_state s10, rdis_of_state s11⟩

theorem A082981_values :
    rdis 4 5 0 = 1 ∧ rdis 4 5 1 = 2 ∧ rdis 4 5 2 = 3 ∧ rdis 4 5 3 = 4 ∧
      rdis 4 5 4 = 9 ∧ rdis 4 5 5 = 14 ∧ rdis 4 5 6 = 19 ∧ rdis 4 5 7 = 24 := by
  decide

/-- Layman (2003): `a(n) = 6 a(n-4) - a(n-8)`. -/
theorem A082981_rec (n : ℕ) : rdis 4 5 (n + 8) + rdis 4 5 n = 6 * rdis 4 5 (n + 4) := by
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ :
      ∃ i, n = 4 * i ∨ n = 4 * i + 1 ∨ n = 4 * i + 2 ∨ n = 4 * i + 3 := ⟨n / 4, by omega⟩
  · obtain ⟨X, Y, r0, -, -, -, r4, -, -, -, r8, -⟩ := A082981_window i
    rw [r0, r4, r8]
    omega
  · obtain ⟨X, Y, -, r1, -, -, -, r5, -, -, -, r9, -⟩ := A082981_window i
    show rdis 4 5 (4 * i + 9) + rdis 4 5 (4 * i + 1) = 6 * rdis 4 5 (4 * i + 5)
    rw [r1, r5, r9]
    omega
  · obtain ⟨X, Y, -, -, r2, -, -, -, r6, -, -, -, r10, -⟩ := A082981_window i
    show rdis 4 5 (4 * i + 10) + rdis 4 5 (4 * i + 2) = 6 * rdis 4 5 (4 * i + 6)
    rw [r2, r6, r10]
    omega
  · obtain ⟨X, Y, -, -, -, r3, -, -, -, r7, -, -, -, r11⟩ := A082981_window i
    show rdis 4 5 (4 * i + 11) + rdis 4 5 (4 * i + 3) = 6 * rdis 4 5 (4 * i + 7)
    rw [r3, r7, r11]
    omega

/-! ### A085260: the ratio `0.0833344` -/

/-- After the first step (`j = 10`) the states stay in the cone `20 Y ≤ 19 X`, where `j = 11` is
forced, and satisfy `11 X² = 11 X Y + Y² + 11`. -/
theorem A085260_base (n : ℕ) :
    ∃ X Y, state 833344 10000000 (n + 1) = (X, Y) ∧ 20 * Y ≤ 19 * X ∧ 0 < Y ∧
      11 * X ^ 2 = 11 * X * Y + Y ^ 2 + 11 := by
  induction n with
  | zero =>
    exact ⟨12, 11, state_step 833344 10000000 0 1 1 10 _ _ (state_zero _ _) (by omega),
      by norm_num, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨X, Y, hs, h1, h2, hq⟩ := ih
    exact ⟨12 * X + Y, 11 * X + Y,
      state_step 833344 10000000 (n + 1) _ _ 11 _ _ hs (by omega), by omega, by omega,
      by nlinarith [hq]⟩

theorem A085260_window (n : ℕ) :
    ∃ X Y, 11 * X ^ 2 = 11 * X * Y + Y ^ 2 + 11 ∧
      rdis 833344 10000000 (n + 1) = X ∧ rdis 833344 10000000 (n + 2) = 12 * X + Y ∧
      rdis 833344 10000000 (n + 3) = 155 * X + 13 * Y ∧
      rdis 833344 10000000 (n + 4) = 2003 * X + 168 * Y := by
  obtain ⟨X, Y, hs, h1, h2, hq⟩ := A085260_base n
  have s2 : state 833344 10000000 (n + 2) = (12 * X + Y, 11 * X + Y) :=
    state_step 833344 10000000 (n + 1) _ _ 11 _ _ hs (by omega)
  have s3 : state 833344 10000000 (n + 3) = (155 * X + 13 * Y, 143 * X + 12 * Y) :=
    state_step 833344 10000000 (n + 2) _ _ 11 _ _ s2 (by omega)
  have s4 : state 833344 10000000 (n + 4) = (2003 * X + 168 * Y, 1848 * X + 155 * Y) :=
    state_step 833344 10000000 (n + 3) _ _ 11 _ _ s3 (by omega)
  exact ⟨X, Y, hq, rdis_of_state hs, rdis_of_state s2, rdis_of_state s3, rdis_of_state s4⟩

theorem A085260_values :
    rdis 833344 10000000 0 = 1 ∧ rdis 833344 10000000 1 = 12 := by
  decide

/-- Layman (2003): `a(n+1) = 13 a(n) - a(n-1)`. -/
theorem A085260_rec (n : ℕ) :
    rdis 833344 10000000 (n + 2) + rdis 833344 10000000 n =
      13 * rdis 833344 10000000 (n + 1) := by
  rcases n with _ | m
  · decide
  · obtain ⟨X, Y, -, r1, r2, r3, -⟩ := A085260_window m
    show rdis 833344 10000000 (m + 3) + rdis 833344 10000000 (m + 1) =
      13 * rdis 833344 10000000 (m + 2)
    rw [r1, r2, r3]
    omega

/-- Stephan (2004): `a(n) a(n+3) = 143 + a(n+1) a(n+2)`. -/
theorem A085260_prod (n : ℕ) :
    rdis 833344 10000000 n * rdis 833344 10000000 (n + 3) =
      143 + rdis 833344 10000000 (n + 1) * rdis 833344 10000000 (n + 2) := by
  rcases n with _ | m
  · decide
  · obtain ⟨X, Y, hq, r1, r2, r3, r4⟩ := A085260_window m
    show rdis 833344 10000000 (m + 1) * rdis 833344 10000000 (m + 4) =
      143 + rdis 833344 10000000 (m + 2) * rdis 833344 10000000 (m + 3)
    rw [r1, r2, r3, r4]
    nlinarith [hq]

/-! ### A085376: the ratio `0.36704` -/

/-- The states with even index stay in the cone `26592 X < 36704 Y`, `Y ≤ X`, where the pattern
`j = 1, 2` is forced, and satisfy `5 X² + 3 = 4 X Y + 4 Y²`. -/
theorem A085376_base (i : ℕ) :
    ∃ X Y, state 36704 100000 (2 * i) = (X, Y) ∧ 26592 * X < 36704 * Y ∧ Y ≤ X ∧
      5 * X ^ 2 + 3 = 4 * X * Y + 4 * Y ^ 2 := by
  induction i with
  | zero => exact ⟨1, 1, state_zero _ _, by norm_num, by norm_num, by norm_num⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, h1, h2, hq⟩ := ih
    have s1 : state 36704 100000 (2 * i + 1) = (2 * X + Y, X + Y) :=
      state_step 36704 100000 (2 * i) _ _ 1 _ _ hs (by omega)
    have s2 : state 36704 100000 (2 * i + 2) = (7 * X + 4 * Y, 5 * X + 3 * Y) :=
      state_step 36704 100000 (2 * i + 1) _ _ 2 _ _ s1 (by omega)
    refine ⟨7 * X + 4 * Y, 5 * X + 3 * Y, ?_, by omega, by omega, by nlinarith [hq]⟩
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    exact s2

theorem A085376_window (i : ℕ) :
    ∃ X Y, 5 * X ^ 2 + 3 = 4 * X * Y + 4 * Y ^ 2 ∧
      rdis 36704 100000 (2 * i) = X ∧ rdis 36704 100000 (2 * i + 1) = 2 * X + Y ∧
      rdis 36704 100000 (2 * i + 2) = 7 * X + 4 * Y ∧
      rdis 36704 100000 (2 * i + 3) = 19 * X + 11 * Y ∧
      rdis 36704 100000 (2 * i + 4) = 69 * X + 40 * Y ∧
      rdis 36704 100000 (2 * i + 5) = 188 * X + 109 * Y := by
  obtain ⟨X, Y, hs, h1, h2, hq⟩ := A085376_base i
  have s1 : state 36704 100000 (2 * i + 1) = (2 * X + Y, X + Y) :=
    state_step 36704 100000 (2 * i) _ _ 1 _ _ hs (by omega)
  have s2 : state 36704 100000 (2 * i + 2) = (7 * X + 4 * Y, 5 * X + 3 * Y) :=
    state_step 36704 100000 (2 * i + 1) _ _ 2 _ _ s1 (by omega)
  have s3 : state 36704 100000 (2 * i + 3) = (19 * X + 11 * Y, 12 * X + 7 * Y) :=
    state_step 36704 100000 (2 * i + 2) _ _ 1 _ _ s2 (by omega)
  have s4 : state 36704 100000 (2 * i + 4) = (69 * X + 40 * Y, 50 * X + 29 * Y) :=
    state_step 36704 100000 (2 * i + 3) _ _ 2 _ _ s3 (by omega)
  have s5 : state 36704 100000 (2 * i + 5) = (188 * X + 109 * Y, 119 * X + 69 * Y) :=
    state_step 36704 100000 (2 * i + 4) _ _ 1 _ _ s4 (by omega)
  exact ⟨X, Y, hq, rdis_of_state hs, rdis_of_state s1, rdis_of_state s2, rdis_of_state s3,
    rdis_of_state s4, rdis_of_state s5⟩

theorem A085376_values :
    rdis 36704 100000 0 = 1 ∧ rdis 36704 100000 1 = 3 ∧ rdis 36704 100000 2 = 11 ∧
      rdis 36704 100000 3 = 30 := by
  decide

/-- Layman (2003): `a(n) = 10 a(n-2) - a(n-4)`. -/
theorem A085376_rec (n : ℕ) :
    rdis 36704 100000 (n + 4) + rdis 36704 100000 n = 10 * rdis 36704 100000 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, -, r0, -, r2, -, r4, -⟩ := A085376_window i
    rw [r0, r2, r4]
    omega
  · obtain ⟨X, Y, -, -, r1, -, r3, -, r5⟩ := A085376_window i
    show rdis 36704 100000 (2 * i + 5) + rdis 36704 100000 (2 * i + 1) =
      10 * rdis 36704 100000 (2 * i + 3)
    rw [r1, r3, r5]
    omega

/-- Stephan (2004): `a(n) a(n+3) = -3 + a(n+1) a(n+2)`. -/
theorem A085376_prod (n : ℕ) :
    rdis 36704 100000 n * rdis 36704 100000 (n + 3) + 3 =
      rdis 36704 100000 (n + 1) * rdis 36704 100000 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, hq, r0, r1, r2, r3, -⟩ := A085376_window i
    rw [r0, r1, r2, r3]
    nlinarith [hq]
  · obtain ⟨X, Y, hq, -, r1, r2, r3, r4, -⟩ := A085376_window i
    show rdis 36704 100000 (2 * i + 1) * rdis 36704 100000 (2 * i + 4) + 3 =
      rdis 36704 100000 (2 * i + 2) * rdis 36704 100000 (2 * i + 3)
    rw [r1, r2, r3, r4]
    nlinarith [hq]

/-! ### A085348: the ratio `0.264` -/

/-- The states with even index stay in the cone `208 X < 264 Y`, `Y ≤ X`, where the pattern
`j = 2, 3` is forced, and satisfy `11 X² + 4 = 10 X Y + 5 Y²`. -/
theorem A085348_base (i : ℕ) :
    ∃ X Y, state 264 1000 (2 * i) = (X, Y) ∧ 208 * X < 264 * Y ∧ Y ≤ X ∧
      11 * X ^ 2 + 4 = 10 * X * Y + 5 * Y ^ 2 := by
  induction i with
  | zero => exact ⟨1, 1, state_zero _ _, by norm_num, by norm_num, by norm_num⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, h1, h2, hq⟩ := ih
    have s1 : state 264 1000 (2 * i + 1) = (3 * X + Y, 2 * X + Y) :=
      state_step 264 1000 (2 * i) _ _ 2 _ _ hs (by omega)
    have s2 : state 264 1000 (2 * i + 2) = (14 * X + 5 * Y, 11 * X + 4 * Y) :=
      state_step 264 1000 (2 * i + 1) _ _ 3 _ _ s1 (by omega)
    refine ⟨14 * X + 5 * Y, 11 * X + 4 * Y, ?_, by omega, by omega, by nlinarith [hq]⟩
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    exact s2

theorem A085348_window (i : ℕ) :
    ∃ X Y, 11 * X ^ 2 + 4 = 10 * X * Y + 5 * Y ^ 2 ∧
      rdis 264 1000 (2 * i) = X ∧ rdis 264 1000 (2 * i + 1) = 3 * X + Y ∧
      rdis 264 1000 (2 * i + 2) = 14 * X + 5 * Y ∧
      rdis 264 1000 (2 * i + 3) = 53 * X + 19 * Y ∧
      rdis 264 1000 (2 * i + 4) = 251 * X + 90 * Y ∧
      rdis 264 1000 (2 * i + 5) = 951 * X + 341 * Y := by
  obtain ⟨X, Y, hs, h1, h2, hq⟩ := A085348_base i
  have s1 : state 264 1000 (2 * i + 1) = (3 * X + Y, 2 * X + Y) :=
    state_step 264 1000 (2 * i) _ _ 2 _ _ hs (by omega)
  have s2 : state 264 1000 (2 * i + 2) = (14 * X + 5 * Y, 11 * X + 4 * Y) :=
    state_step 264 1000 (2 * i + 1) _ _ 3 _ _ s1 (by omega)
  have s3 : state 264 1000 (2 * i + 3) = (53 * X + 19 * Y, 39 * X + 14 * Y) :=
    state_step 264 1000 (2 * i + 2) _ _ 2 _ _ s2 (by omega)
  have s4 : state 264 1000 (2 * i + 4) = (251 * X + 90 * Y, 198 * X + 71 * Y) :=
    state_step 264 1000 (2 * i + 3) _ _ 3 _ _ s3 (by omega)
  have s5 : state 264 1000 (2 * i + 5) = (951 * X + 341 * Y, 700 * X + 251 * Y) :=
    state_step 264 1000 (2 * i + 4) _ _ 2 _ _ s4 (by omega)
  exact ⟨X, Y, hq, rdis_of_state hs, rdis_of_state s1, rdis_of_state s2, rdis_of_state s3,
    rdis_of_state s4, rdis_of_state s5⟩

theorem A085348_values :
    rdis 264 1000 0 = 1 ∧ rdis 264 1000 1 = 4 ∧ rdis 264 1000 2 = 19 ∧ rdis 264 1000 3 = 72 := by
  decide

/-- Layman (2003): `a(n) = 18 a(n-2) - a(n-4)`. -/
theorem A085348_rec (n : ℕ) :
    rdis 264 1000 (n + 4) + rdis 264 1000 n = 18 * rdis 264 1000 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, -, r0, -, r2, -, r4, -⟩ := A085348_window i
    rw [r0, r2, r4]
    omega
  · obtain ⟨X, Y, -, -, r1, -, r3, -, r5⟩ := A085348_window i
    show rdis 264 1000 (2 * i + 5) + rdis 264 1000 (2 * i + 1) = 18 * rdis 264 1000 (2 * i + 3)
    rw [r1, r3, r5]
    omega

/-- Stephan (2004): `a(n) a(n+3) = -4 + a(n+1) a(n+2)`. -/
theorem A085348_prod (n : ℕ) :
    rdis 264 1000 n * rdis 264 1000 (n + 3) + 4 =
      rdis 264 1000 (n + 1) * rdis 264 1000 (n + 2) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨X, Y, hq, r0, r1, r2, r3, -⟩ := A085348_window i
    rw [r0, r1, r2, r3]
    nlinarith [hq]
  · obtain ⟨X, Y, hq, -, r1, r2, r3, r4, -⟩ := A085348_window i
    show rdis 264 1000 (2 * i + 1) * rdis 264 1000 (2 * i + 4) + 4 =
      rdis 264 1000 (2 * i + 2) * rdis 264 1000 (2 * i + 3)
    rw [r1, r2, r3, r4]
    nlinarith [hq]

/-! ### A085349: the ratio `0.26688` -/

/-- After the first step (`j = 2`) the states with odd index stay in the cone
`19936 X < 26688 Y`, `6752 Y ≤ 6432 X`, where the pattern `j = 2, 3` is forced, and satisfy
`11 X² = 11 + 10 X Y + 5 Y²`. -/
theorem A085349_base (i : ℕ) :
    ∃ X Y, state 26688 100000 (2 * i + 1) = (X, Y) ∧ 19936 * X < 26688 * Y ∧
      6752 * Y ≤ 6432 * X ∧ 11 * X ^ 2 = 11 + 10 * X * Y + 5 * Y ^ 2 := by
  induction i with
  | zero =>
    exact ⟨4, 3, state_step 26688 100000 0 1 1 2 _ _ (state_zero _ _) (by omega),
      by norm_num, by norm_num, by norm_num⟩
  | succ i ih =>
    obtain ⟨X, Y, hs, h1, h2, hq⟩ := ih
    have s1 : state 26688 100000 (2 * i + 2) = (3 * X + Y, 2 * X + Y) :=
      state_step 26688 100000 (2 * i + 1) _ _ 2 _ _ hs (by omega)
    have s2 : state 26688 100000 (2 * i + 3) = (14 * X + 5 * Y, 11 * X + 4 * Y) :=
      state_step 26688 100000 (2 * i + 2) _ _ 3 _ _ s1 (by omega)
    refine ⟨14 * X + 5 * Y, 11 * X + 4 * Y, ?_, by omega, by omega, by nlinarith [hq]⟩
    rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
    exact s2

theorem A085349_window (i : ℕ) :
    ∃ X Y, 11 * X ^ 2 = 11 + 10 * X * Y + 5 * Y ^ 2 ∧
      rdis 26688 100000 (2 * i + 1) = X ∧ rdis 26688 100000 (2 * i + 2) = 3 * X + Y ∧
      rdis 26688 100000 (2 * i + 3) = 14 * X + 5 * Y ∧
      rdis 26688 100000 (2 * i + 4) = 53 * X + 19 * Y ∧
      rdis 26688 100000 (2 * i + 5) = 251 * X + 90 * Y ∧
      rdis 26688 100000 (2 * i + 6) = 951 * X + 341 * Y := by
  obtain ⟨X, Y, hs, h1, h2, hq⟩ := A085349_base i
  have s2 : state 26688 100000 (2 * i + 2) = (3 * X + Y, 2 * X + Y) :=
    state_step 26688 100000 (2 * i + 1) _ _ 2 _ _ hs (by omega)
  have s3 : state 26688 100000 (2 * i + 3) = (14 * X + 5 * Y, 11 * X + 4 * Y) :=
    state_step 26688 100000 (2 * i + 2) _ _ 3 _ _ s2 (by omega)
  have s4 : state 26688 100000 (2 * i + 4) = (53 * X + 19 * Y, 39 * X + 14 * Y) :=
    state_step 26688 100000 (2 * i + 3) _ _ 2 _ _ s3 (by omega)
  have s5 : state 26688 100000 (2 * i + 5) = (251 * X + 90 * Y, 198 * X + 71 * Y) :=
    state_step 26688 100000 (2 * i + 4) _ _ 3 _ _ s4 (by omega)
  have s6 : state 26688 100000 (2 * i + 6) = (951 * X + 341 * Y, 700 * X + 251 * Y) :=
    state_step 26688 100000 (2 * i + 5) _ _ 2 _ _ s5 (by omega)
  exact ⟨X, Y, hq, rdis_of_state hs, rdis_of_state s2, rdis_of_state s3, rdis_of_state s4,
    rdis_of_state s5, rdis_of_state s6⟩

theorem A085349_values :
    rdis 26688 100000 0 = 1 ∧ rdis 26688 100000 1 = 4 ∧ rdis 26688 100000 2 = 15 ∧
      rdis 26688 100000 3 = 71 := by
  decide

/-- Layman (2003): `a(n) = 18 a(n-2) - a(n-4)`. -/
theorem A085349_rec (n : ℕ) :
    rdis 26688 100000 (n + 4) + rdis 26688 100000 n = 18 * rdis 26688 100000 (n + 2) := by
  rcases n with _ | m
  · decide
  · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
    · obtain ⟨X, Y, -, r1, -, r3, -, r5, -⟩ := A085349_window i
      show rdis 26688 100000 (2 * i + 5) + rdis 26688 100000 (2 * i + 1) =
        18 * rdis 26688 100000 (2 * i + 3)
      rw [r1, r3, r5]
      omega
    · obtain ⟨X, Y, -, -, r2, -, r4, -, r6⟩ := A085349_window i
      show rdis 26688 100000 (2 * i + 6) + rdis 26688 100000 (2 * i + 2) =
        18 * rdis 26688 100000 (2 * i + 4)
      rw [r2, r4, r6]
      omega

/-- Stephan (2004): `a(n) a(n+3) = 11 + a(n+1) a(n+2)`. -/
theorem A085349_prod (n : ℕ) :
    rdis 26688 100000 n * rdis 26688 100000 (n + 3) =
      11 + rdis 26688 100000 (n + 1) * rdis 26688 100000 (n + 2) := by
  rcases n with _ | m
  · decide
  · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
    · obtain ⟨X, Y, hq, r1, r2, r3, r4, -⟩ := A085349_window i
      show rdis 26688 100000 (2 * i + 1) * rdis 26688 100000 (2 * i + 4) =
        11 + rdis 26688 100000 (2 * i + 2) * rdis 26688 100000 (2 * i + 3)
      rw [r1, r2, r3, r4]
      nlinarith [hq]
    · obtain ⟨X, Y, hq, -, r2, r3, r4, r5, -⟩ := A085349_window i
      show rdis 26688 100000 (2 * i + 2) * rdis 26688 100000 (2 * i + 5) =
        11 + rdis 26688 100000 (2 * i + 3) * rdis 26688 100000 (2 * i + 4)
      rw [r2, r3, r4, r5]
      nlinarith [hq]

end Insertion
