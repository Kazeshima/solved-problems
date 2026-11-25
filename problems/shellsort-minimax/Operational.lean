import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

/-! Ordinary insertion into a residue chain. The sorted prefix is stored in
reverse physical order. Every visit to a nonempty prefix executes one comparison.
The trace records the rank being inserted at each such comparison. -/
namespace ShellMinimax.Operational

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

def ins (a : α) : List α → List α × Nat
  | [] => ([a], 0)
  | y :: ys =>
    if y ≤ a then (a :: y :: ys, 1)
    else let p := ins a ys
         (y :: p.1, p.2 + 1)

def chain : List α → List α × List α
  | [] => ([], [])
  | a :: as =>
    let p := chain as
    let q := ins a p.1
    (q.1, p.2 ++ List.replicate q.2 a)

theorem ins_values (a : α) (l : List α) :
    (ins a l).1 = l.orderedInsert (· ≥ ·) a := by
  induction l with
  | nil => rfl
  | cons y ys ih => by_cases h : y ≤ a <;> simp [ins, List.orderedInsert, h, ih]

theorem chain_values (l : List α) :
    (chain l).1 = l.insertionSort (· ≥ ·) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [chain, ins_values, ih, List.insertionSort]

theorem map_values (f : α → β) (hf : Monotone f) (l : List α) :
    (chain (l.map f)).1 = (chain l).1.map f := by
  simp only [chain_values]
  apply List.eq_of_perm_of_sorted (r := (· ≥ ·))
  · exact (List.perm_insertionSort _ _).trans ((List.perm_insertionSort _ l).map f).symm
  · apply List.sorted_insertionSort
  · exact List.pairwise_map.mpr ((List.sorted_insertionSort (· ≥ ·) l).imp fun h => hf h)

theorem ins_count_map (f : α → β) (a : α) (test : ∀ y, f y ≤ f a ↔ y ≤ a)
    (l : List α) : (ins (f a) (l.map f)).2 = (ins a l).2 := by
  induction l with
  | nil => rfl
  | cons y ys ih => by_cases h : y ≤ a <;> simp [ins, test, h, ih]

/-- Counts the actual loop visits, including the stopping comparison. -/
theorem ins_count (a : α) (l : List α) (hs : l.Pairwise (· ≥ ·)) :
    (ins a l).2 = l.length - (l.filter (· ≤ a)).length +
      (if 0 < (l.filter (· ≤ a)).length then 1 else 0) := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    obtain ⟨hy, ht⟩ := List.pairwise_cons.mp hs
    by_cases h : y ≤ a
    · have hall : ys.filter (· ≤ a) = ys := List.filter_eq_self.mpr
          (fun z hz => by simpa using (hy z hz).trans h)
      simp [ins, h, hall]
    · have hh := ih ht
      have hlen := List.length_filter_le (fun z : α => decide (z ≤ a)) ys
      simp [ins, h] at *
      omega

theorem chain_mark (f : α → β) (hf : Monotone f) (a : α) (b : β)
    (mark : ∀ y, f y = b ↔ y = a) (test : ∀ y, f y ≤ f a ↔ y ≤ a)
    (l : List α) : (chain (l.map f)).2.count b = (chain l).2.count a := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y = a
    · subst y
      have he := (mark a).mpr rfl
      subst b
      simp [chain, ih, map_values f hf, ins_count_map f a test]
    · have he : f y ≠ b := fun he => h ((mark y).mp he)
      simp [chain, List.count_replicate, h, he, ih]

variable {n : Nat}

def slots (n h r : Nat) : List (Fin n) :=
  (List.finRange n).filter fun i => i.val % h == r

def bucket (A : Fin n → α) (h r : Nat) : List α × List α :=
  chain (((slots n h r).map A).reverse)

def pass (A : Fin n → α) (h : Nat) : Fin n → α := fun x =>
  ((bucket A h (x.val % h)).1.reverse).getD (x.val / h) (A x)

def passTrace (A : Fin n → α) (h : Nat) : List α :=
  (List.range h).flatMap fun r => (bucket A h r).2

def trace (A : Fin n → α) : List Nat → List α
  | [] => []
  | h :: hs => passTrace A h ++ trace (pass A h) hs

theorem bucket_map (f : α → β) (hf : Monotone f) (A : Fin n → α) (h r : Nat) :
    (bucket (f ∘ A) h r).1 = (bucket A h r).1.map f := by
  simpa [bucket, List.map_reverse, List.map_map] using
    map_values f hf (((slots n h r).map A).reverse)

theorem pass_map (f : α → β) (hf : Monotone f) (A : Fin n → α) (h : Nat) :
    pass (f ∘ A) h = f ∘ pass A h := by
  funext x
  simp only [pass, bucket_map f hf, ← List.map_reverse, Function.comp_apply]
  apply List.getD_map

theorem trace_mark (f : α → β) (hf : Monotone f) (a : α) (b : β)
    (mark : ∀ y, f y = b ↔ y = a) (test : ∀ y, f y ≤ f a ↔ y ≤ a)
    (A : Fin n → α) (gaps : List Nat) :
    (trace (f ∘ A) gaps).count b = (trace A gaps).count a := by
  induction gaps generalizing A with
  | nil => rfl
  | cons h hs ih =>
    simp only [trace, List.count_append, pass_map f hf, ih]
    congr 1
    simp only [passTrace, List.count_flatMap]
    congr 1
    apply List.map_congr_left
    intro r _
    simpa [bucket, List.map_reverse, List.map_map] using
      chain_mark f hf a b mark test (((slots n h r).map A).reverse)

end ShellMinimax.Operational
