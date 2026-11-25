import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

/-! Bellman bounds, viability and arithmetic threshold edges. The operational equivalence is proved in Charging.lean. -/
namespace ShellMinimax

section Bellman
variable {α σ : Type*}

/-- Maximum of a list of natural-number costs (0 for the empty list). -/
def maxCost : List Nat → Nat
  | [] => 0
  | a :: t => max a (maxCost t)

theorem le_maxCost_of_mem {v : Nat} {l : List Nat} (hv : v ∈ l) : v ≤ maxCost l := by
  induction l with
  | nil => simp at hv
  | cons a t ih =>
    change v ≤ max a (maxCost t)
    rcases List.mem_cons.mp hv with heq | hm
    · subst v
      exact le_max_left _ _
    · exact (ih hm).trans (le_max_right _ _)

theorem maxCost_mem {l : List Nat} (hn : l ≠ []) : maxCost l ∈ l := by
  induction l with
  | nil => exact (hn rfl).elim
  | cons a t ih =>
    cases t with
    | nil => simp [maxCost]
    | cons b t =>
      have ht : maxCost (b :: t) ∈ b :: t := ih (by simp)
      change max a (maxCost (b :: t)) ∈ a :: b :: t
      rcases le_total a (maxCost (b :: t)) with h | h
      · rw [max_eq_right h]
        exact List.mem_cons_of_mem _ ht
      · rw [max_eq_left h]
        simp

variable (options : σ → List α) (move : σ → α → σ) (weight : σ → α → Nat)

/-- An executable recurrence; memoization is an implementation detail. -/
def bellman : Nat → σ → Nat
  | 0, _ => 0
  | k+1, s => maxCost ((options s).map fun x => weight s x + bellman k (move s x))

def walkCost : σ → List α → Nat
  | _, [] => 0
  | s, x :: xs => weight s x + walkCost (move s x) xs

inductive Walk : Nat → σ → List α → Prop
  | nil (s : σ) : Walk 0 s []
  | cons {k : Nat} {s : σ} {x : α} {xs : List α}
      (hx : x ∈ options s) (ht : Walk k (move s x) xs) : Walk (k+1) s (x :: xs)

/-- Every path of the required length has cost at most the recurrence. -/
theorem walk_le_bellman {k : Nat} {s : σ} {xs : List α}
    (hw : Walk options move k s xs) : walkCost move weight s xs ≤ bellman options move weight k s := by
  induction hw with
  | nil s => rfl
  | @cons k s x xs hx ht ih =>
    change weight s x + walkCost move weight (move s x) xs ≤
      maxCost ((options s).map fun y => weight s y + bellman options move weight k (move s y))
    have hm : weight s x + bellman options move weight k (move s x) ∈
        (options s).map (fun y => weight s y + bellman options move weight k (move s y)) :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    exact (Nat.add_le_add_left ih _).trans (le_maxCost_of_mem hm)

/-- There is a continuation of every required length along all choices. -/
def Viable : Nat → σ → Prop
  | 0, _ => True
  | k+1, s => options s ≠ [] ∧ ∀ x ∈ options s, Viable k (move s x)

/-- The recurrence attains its bound when no path stops prematurely. -/
theorem bellman_attained (k : Nat) (s : σ) (hv : Viable options move k s) :
    ∃ xs, Walk options move k s xs ∧ walkCost move weight s xs = bellman options move weight k s := by
  induction k generalizing s with
  | zero => exact ⟨[], Walk.nil s, rfl⟩
  | succ k ih =>
    change options s ≠ [] ∧ ∀ x ∈ options s, Viable options move k (move s x) at hv
    let l := (options s).map (fun x => weight s x + bellman options move weight k (move s x))
    have hn : l ≠ [] := by
      intro he
      apply hv.1
      simpa [l] using he
    have hm : maxCost l ∈ l := maxCost_mem hn
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    obtain ⟨xs, hwalk, hcost⟩ := ih (move s x) (hv.2 x hx)
    refine ⟨x :: xs, Walk.cons hx hwalk, ?_⟩
    change weight s x + walkCost move weight (move s x) xs = maxCost l
    rw [hcost]
    exact he

end Bellman

section Subsets

variable (n : Nat)

/-- All unused positions, ordered only to get an executable enumeration. -/
noncomputable def unused (s : Finset (Fin n)) : List (Fin n) :=
  (Finset.univ \ s).toList

def addPosition (s : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := insert x s

theorem unused_spec (s : Finset (Fin n)) (x : Fin n) : x ∈ unused n s ↔ x ∉ s := by
  simp [unused]

/-- The rank-ordered choice of positions is a full subset-lattice walk. -/
theorem subset_viable (k : Nat) (s : Finset (Fin n)) (hs : s.card + k = n) :
    Viable (unused n) (addPosition n) k s := by
  induction k generalizing s with
  | zero => trivial
  | succ k ih =>
    change unused n s ≠ [] ∧ ∀ x ∈ unused n s,
      Viable (unused n) (addPosition n) k (addPosition n s x)
    constructor
    · have hex : ∃ x : Fin n, x ∉ s := by
        by_contra h
        push_neg at h
        have hu : s = Finset.univ := by ext x; simp [h x]
        rw [hu] at hs
        simp at hs
      obtain ⟨x, hx⟩ := hex
      have hm := (unused_spec n s x).mpr hx
      intro he
      rw [he] at hm
      simp at hm
    · intro x hx
      have hnot := (unused_spec n s x).mp hx
      apply ih
      have hc : (addPosition n s x).card = s.card + 1 := by
        simp [addPosition, hnot]
      rw [hc]
      omega

/-- Any edge weights on the subset lattice have an attained maximum. -/
theorem subset_bellman_exact (weight : Finset (Fin n) → Fin n → Nat) :
    (∀ xs, Walk (unused n) (addPosition n) n ∅ xs →
      walkCost (addPosition n) weight ∅ xs ≤ bellman (unused n) (addPosition n) weight n ∅) ∧
    ∃ xs, Walk (unused n) (addPosition n) n ∅ xs ∧
      walkCost (addPosition n) weight ∅ xs = bellman (unused n) (addPosition n) weight n ∅ := by
  constructor
  · intro xs h
    exact walk_le_bellman (unused n) (addPosition n) weight h
  · apply bellman_attained (unused n) (addPosition n) weight
    apply subset_viable n
    simp

/-- Count of selected small positions in the residue chain of x. -/
def chainCount (h : Nat) (s : Finset (Fin n)) (x : Fin n) : Nat :=
  (s.filter fun y => y.val % h = x.val % h).card

/-- Binary h-sort puts all selected (small) positions first in each chain. -/
def binaryPass (h : Nat) (s : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => x.val / h < chainCount n h s x

theorem binaryPass_mono (h : Nat) {s t : Finset (Fin n)} (hst : s ⊆ t) :
    binaryPass n h s ⊆ binaryPass n h t := by
  intro x hx
  have hxs : x.val / h < chainCount n h s x := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply lt_of_lt_of_le hxs
  unfold chainCount
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hys, hr⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hst hys, hr⟩

/-- Number of comparisons charged to an insertion with t predecessors,
    of which s are smaller. The operational bridge is proved in ShellMinimax.pass_charge. -/
def insertionCharge (t s : Nat) : Nat := t - s + (if 0 < s then 1 else 0)

theorem insertionCharge_le (t s : Nat) (hs : s ≤ t) : insertionCharge t s ≤ t := by
  unfold insertionCharge
  split <;> omega

/-- Count smaller predecessors in the same residue chain at a natural position. -/
def earlierSmall (h : Nat) (s : Finset (Fin n)) (pos : Nat) : Nat :=
  (s.filter fun y => y.val < pos ∧ y.val % h = pos % h).card

/-- Location of the newly inserted threshold element after a binary pass. -/
def nextRankPosition (h : Nat) (s : Finset (Fin n)) (pos : Nat) : Nat :=
  pos % h + h * (s.filter fun y => y.val % h = pos % h).card

/-- Explicit local edge weights for the Boolean-lattice model. -/
def edgeWeight : List Nat → Finset (Fin n) → Nat → Nat
  | [], _, _ => 0
  | h :: hs, s, pos =>
    insertionCharge (pos / h) (earlierSmall n h s pos) +
      edgeWeight hs (binaryPass n h s) (nextRankPosition n h s pos)

noncomputable def thresholdMaximum (gaps : List Nat) : Nat :=
  bellman (unused n) (addPosition n) (fun s (x : Fin n) => edgeWeight n gaps s x.val) n ∅

/-- Exact optimum of the threshold-path model. This is not yet the theorem
    relating that model to literal executed Shellsort comparisons. -/
theorem thresholdMaximum_exact (gaps : List Nat) :
    (∀ xs, Walk (unused n) (addPosition n) n ∅ xs →
      walkCost (addPosition n) (fun s (x : Fin n) => edgeWeight n gaps s x.val) ∅ xs ≤
        thresholdMaximum n gaps) ∧
    ∃ xs, Walk (unused n) (addPosition n) n ∅ xs ∧
      walkCost (addPosition n) (fun s (x : Fin n) => edgeWeight n gaps s x.val) ∅ xs =
        thresholdMaximum n gaps := by
  exact subset_bellman_exact n _

end Subsets

end ShellMinimax
