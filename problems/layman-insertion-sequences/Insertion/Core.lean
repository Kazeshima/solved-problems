/-
Ratio-determined insertion sequences (J. W. Layman, 2003).

Start with the finite sequence `(1, 1)`.  One pass inserts, between every two adjacent terms
`a, b` with `k * b ≤ a`, their sum `a + b`.  The passes are repeated for ever and the insertion
sequence `I(k)` is the termwise limit.  Here the ratio is `k = p / q` with `0 < p ≤ q`.

This file contains the definitions and the reduction of the limit to a two-variable process.
-/
import Mathlib

namespace Insertion

/-- One insertion pass for the ratio `p / q`: the sum `a + b` is inserted between adjacent
terms `a, b` exactly when `p * b ≤ q * a`. -/
def pass (p q : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
      if p * b ≤ q * a then a :: (a + b) :: pass p q (b :: l) else a :: pass p q (b :: l)

/-- The sequence after `n` passes, starting from `(1, 1)`. -/
def stage (p q n : ℕ) : List ℕ := (pass p q)^[n] [1, 1]

/-- `a` is the termwise limit of the stages: every position is eventually constant, with value
`a i` (positions are counted from `0`). -/
def IsLimit (p q : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ i, ∃ N, ∀ n, N ≤ n → (stage p q n)[i]? = some (a i)

/-- A state `(X, Y)` records a settled term `X` whose right neighbour is `X + Y`, the term after
that being `Y`.  `runLen` is the number of further insertions made directly to the right of `X`
before its neighbour settles. -/
def runLen (p q X Y : ℕ) : ℕ :=
  if p * (X + Y) ≤ q * X then (q * X - p * (X + Y)) / (p * X) + 1 else 0

/-- The state reached when the next term has settled. -/
def next (p q : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  (s.1 + (s.2 + runLen p q s.1 s.2 * s.1), s.2 + runLen p q s.1 s.2 * s.1)

/-- The state after `n` terms have settled. -/
def state (p q n : ℕ) : ℕ × ℕ := (next p q)^[n] (1, 1)

/-- The insertion sequence `I(p / q)`, with positions counted from `0`. -/
def rdis (p q n : ℕ) : ℕ := (state p q n).1

/-! ### The run length -/

/-- Characterisation of `runLen`: the insertions `0, …, runLen - 1` to the right of `X` are
allowed and insertion number `runLen` is refused. -/
private theorem runLen_spec (p q X Y : ℕ) (hp : 0 < p) (hX : 0 < X) :
    (∀ i, i < runLen p q X Y → p * (X + (Y + i * X)) ≤ q * X) ∧
      ¬ p * (X + (Y + runLen p q X Y * X)) ≤ q * X := by
  by_cases h : p * (X + Y) ≤ q * X
  · have hpX : 0 < p * X := Nat.mul_pos hp hX
    have hdm := Nat.div_add_mod (q * X - p * (X + Y)) (p * X)
    have hml := Nat.mod_lt (q * X - p * (X + Y)) hpX
    have hr : runLen p q X Y = (q * X - p * (X + Y)) / (p * X) + 1 := by
      simp only [runLen, if_pos h]
    rw [hr]
    generalize (q * X - p * (X + Y)) / (p * X) = d at hdm ⊢
    constructor
    · intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.mp hi
      have h3 : p * X * i ≤ p * X * d := Nat.mul_le_mul_left _ hid
      have e : p * (X + (Y + i * X)) = p * (X + Y) + p * X * i := by ring
      rw [e]
      omega
    · have e : p * (X + (Y + (d + 1) * X)) = p * (X + Y) + (p * X * d + p * X) := by ring
      rw [e]
      omega
  · have hr : runLen p q X Y = 0 := by
      simp only [runLen, if_neg h]
    rw [hr]
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    rw [Nat.zero_mul, Nat.add_zero]
    exact h

/-- `runLen` is the only number with the property of `runLen_spec`. -/
private theorem runLen_eq (p q X Y j : ℕ) (hp : 0 < p) (hX : 0 < X)
    (h1 : j = 0 ∨ p * (Y + j * X) ≤ q * X) (h2 : q * X < p * (X + Y + j * X)) :
    runLen p q X Y = j := by
  obtain ⟨ha, hb⟩ := runLen_spec p q X Y hp hX
  generalize runLen p q X Y = r at ha hb ⊢
  rcases Nat.lt_trichotomy r j with hlt | heq | hgt
  · exfalso
    apply hb
    rcases h1 with h0 | h1
    · omega
    · have h3 : (r + 1) * X ≤ j * X := Nat.mul_le_mul_right X (Nat.succ_le_of_lt hlt)
      have e : (r + 1) * X = r * X + X := by ring
      have h4 : X + (Y + r * X) ≤ Y + j * X := by omega
      exact le_trans (Nat.mul_le_mul_left p h4) h1
  · exact heq
  · exfalso
    have h3 := ha j hgt
    have e : X + (Y + j * X) = X + Y + j * X := by ring
    rw [e] at h3
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h3)

/-- A description of one step of the process that does not mention `runLen`: if `j` further
insertions are made (`j = 0`, or the `j`-th one is allowed) and the next one is refused, then the
new state is `(X + Y + j * X, Y + j * X)`. -/
theorem next_eq (p q X Y j : ℕ) (hp : 0 < p) (hX : 0 < X)
    (h1 : j = 0 ∨ p * (Y + j * X) ≤ q * X) (h2 : q * X < p * (X + Y + j * X)) :
    next p q (X, Y) = (X + Y + j * X, Y + j * X) := by
  have hr := runLen_eq p q X Y j hp hX h1 h2
  show (X + (Y + runLen p q X Y * X), Y + runLen p q X Y * X) = (X + Y + j * X, Y + j * X)
  rw [hr, Nat.add_assoc]

theorem state_zero (p q : ℕ) : state p q 0 = (1, 1) := rfl

theorem state_succ (p q n : ℕ) : state p q (n + 1) = next p q (state p q n) := by
  simp [state, Function.iterate_succ_apply']

theorem state_add (p q m n : ℕ) : state p q (m + n) = (next p q)^[m] (state p q n) := by
  simp [state, Function.iterate_add_apply]

private theorem state_fst_pos (p q n : ℕ) : 0 < (state p q n).1 := by
  induction n with
  | zero =>
    rw [state_zero]
    exact Nat.one_pos
  | succ n ih =>
    rw [state_succ]
    exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)

/-! ### One pass -/

private theorem pass_cons_cons_pos {p q a b : ℕ} (l : List ℕ) (h : p * b ≤ q * a) :
    pass p q (a :: b :: l) = a :: (a + b) :: pass p q (b :: l) := by
  simp only [pass, if_pos h]

private theorem pass_cons_cons_neg {p q a b : ℕ} (l : List ℕ) (h : ¬ p * b ≤ q * a) :
    pass p q (a :: b :: l) = a :: pass p q (b :: l) := by
  simp only [pass, if_neg h]

/-- A pass never changes the first term. -/
private theorem pass_cons (p q a : ℕ) (l : List ℕ) : ∃ T, pass p q (a :: l) = a :: T := by
  cases l with
  | nil => exact ⟨[], by simp only [pass]⟩
  | cons b l =>
    by_cases h : p * b ≤ q * a
    · exact ⟨_, pass_cons_cons_pos l h⟩
    · exact ⟨_, pass_cons_cons_neg l h⟩

private theorem stage_add (p q m n : ℕ) : stage p q (m + n) = (pass p q)^[m] (stage p q n) := by
  unfold stage
  exact Function.iterate_add_apply _ _ _ _

/-- If a pass does not touch the prefix `P ++ [X]`, neither does any number of passes. -/
private theorem pass_iterate_prefix {p q : ℕ} {P : List ℕ} {X : ℕ}
    (hS : ∀ T, pass p q (P ++ X :: T) = P ++ pass p q (X :: T)) (m : ℕ) :
    ∀ T, ∃ T', (pass p q)^[m] (P ++ X :: T) = P ++ X :: T' := by
  induction m with
  | zero => exact fun T => ⟨T, rfl⟩
  | succ m ih =>
    intro T
    obtain ⟨T₁, h₁⟩ := ih T
    obtain ⟨T₂, h₂⟩ := pass_cons p q X T₁
    exact ⟨T₂, by rw [Function.iterate_succ_apply', h₁, hS, h₂]⟩

/-! ### The invariant

`Inv p q P X Y l`: the list `l` is `P ++ X :: (X + Y) :: Y :: T`, where the prefix `P ++ [X]` is
settled, i.e. it is not changed by a pass, whatever follows it. -/

private structure Inv (p q : ℕ) (P : List ℕ) (X Y : ℕ) (l : List ℕ) : Prop where
  stable : ∀ T, pass p q (P ++ X :: T) = P ++ pass p q (X :: T)
  eq : ∃ T, l = P ++ X :: (X + Y) :: Y :: T

/-- An insertion is made to the right of `X`: the state `(X, Y)` becomes `(X, X + Y)`. -/
private theorem Inv.stepR {p q : ℕ} (hpq : p ≤ q) {P : List ℕ} {X Y : ℕ} {l : List ℕ}
    (h : Inv p q P X Y l) (hc : p * (X + Y) ≤ q * X) :
    Inv p q P X (X + Y) (pass p q l) := by
  obtain ⟨hS, T, rfl⟩ := h
  have h2 : p * Y ≤ q * (X + Y) :=
    le_trans (Nat.mul_le_mul_right Y hpq) (Nat.mul_le_mul_left q (Nat.le_add_left Y X))
  refine ⟨hS, (X + Y + Y) :: pass p q (Y :: T), ?_⟩
  rw [hS, pass_cons_cons_pos _ hc, pass_cons_cons_pos _ h2]

/-- No insertion is made to the right of `X`: its neighbour `X + Y` is settled and the state
`(X, Y)` becomes `(X + Y, Y)`. -/
private theorem Inv.stepL {p q : ℕ} (hpq : p ≤ q) {P : List ℕ} {X Y : ℕ} {l : List ℕ}
    (h : Inv p q P X Y l) (hc : ¬ p * (X + Y) ≤ q * X) :
    Inv p q (P ++ [X]) (X + Y) Y (pass p q l) := by
  obtain ⟨hS, T, rfl⟩ := h
  have h2 : p * Y ≤ q * (X + Y) :=
    le_trans (Nat.mul_le_mul_right Y hpq) (Nat.mul_le_mul_left q (Nat.le_add_left Y X))
  obtain ⟨T', hT'⟩ := pass_cons p q Y T
  refine ⟨fun T₂ => ?_, T', ?_⟩
  · have e : (P ++ [X]) ++ (X + Y) :: T₂ = P ++ X :: (X + Y) :: T₂ := by simp
    rw [e, hS, pass_cons_cons_neg _ hc]
    simp
  · rw [hS, pass_cons_cons_neg _ hc, pass_cons_cons_pos _ h2, hT']
    simp

/-- `j` consecutive insertions to the right of `X`. -/
private theorem Inv.run {p q : ℕ} (hpq : p ≤ q) {P : List ℕ} {X Y : ℕ} {l : List ℕ}
    (h : Inv p q P X Y l) (j : ℕ) (hj : ∀ i, i < j → p * (X + (Y + i * X)) ≤ q * X) :
    Inv p q P X (Y + j * X) ((pass p q)^[j] l) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have h1 := ih (fun i hi => hj i (Nat.lt_succ_of_lt hi))
    have h2 := Inv.stepR hpq h1 (hj j (Nat.lt_succ_self j))
    have e : Y + (j + 1) * X = X + (Y + j * X) := by ring
    rw [Function.iterate_succ_apply', e]
    exact h2

/-- For every `c` there is a stage at which the first `c` terms are settled and the two-variable
process is in the state `state p q c`. -/
private theorem reach (p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) (c : ℕ) :
    ∃ n P, P.length = c ∧ Inv p q P (state p q c).1 (state p q c).2 (stage p q n) := by
  induction c with
  | zero =>
    have h : p * 1 ≤ q * 1 := Nat.mul_le_mul_right 1 hpq
    refine ⟨1, [], rfl, fun T => rfl, [], ?_⟩
    rw [stage, Function.iterate_one, pass_cons_cons_pos _ h]
    simp [pass, state_zero]
  | succ c ih =>
    obtain ⟨n, P, hlen, hInv⟩ := ih
    obtain ⟨ha, hb⟩ :=
      runLen_spec p q (state p q c).1 (state p q c).2 hp (state_fst_pos p q c)
    have h1 := Inv.run hpq hInv (runLen p q (state p q c).1 (state p q c).2) ha
    have h2 := Inv.stepL hpq h1 hb
    refine ⟨runLen p q (state p q c).1 (state p q c).2 + 1 + n, P ++ [(state p q c).1], ?_, ?_⟩
    · simp [hlen]
    · rw [state_succ, stage_add, Function.iterate_succ_apply']
      exact h2

/-- **Reduction.**  For `0 < p ≤ q` the termwise limit of the insertion passes exists and is the
sequence produced by the two-variable process. -/
theorem isLimit_rdis (p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) : IsLimit p q (rdis p q) := by
  intro i
  obtain ⟨n, P, hlen, hS, T, hT⟩ := reach p q hp hpq i
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨T', hT'⟩ :=
    pass_iterate_prefix hS k (((state p q i).1 + (state p q i).2) :: (state p q i).2 :: T)
  rw [Nat.add_comm n k, stage_add, hT, hT', List.getElem?_append_right (le_of_eq hlen)]
  simp [hlen, rdis]

/-- The limit is unique. -/
theorem IsLimit.unique {p q : ℕ} {a b : ℕ → ℕ} (ha : IsLimit p q a) (hb : IsLimit p q b) :
    a = b := by
  funext i
  obtain ⟨N₁, h₁⟩ := ha i
  obtain ⟨N₂, h₂⟩ := hb i
  have e₁ := h₁ (max N₁ N₂) (le_max_left _ _)
  have e₂ := h₂ (max N₁ N₂) (le_max_right _ _)
  rw [e₁] at e₂
  exact Option.some.inj e₂

end Insertion
