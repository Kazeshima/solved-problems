import BooleanLattice
import Operational
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.SplitIfs

namespace ShellMinimax
open Operational

variable {n : Nat}

/-- Three colours isolate the comparisons charged to a single rank. -/
def colour (k a : Fin n) : Nat := if a < k then 0 else if a = k then 1 else 2

theorem colour_mono (k : Fin n) : Monotone (colour k) := by
  intro x y h
  simp only [colour]
  split_ifs <;> omega

theorem colour_one (k a : Fin n) : colour k a = 1 ↔ a = k := by
  by_cases h : a = k
  · simp [h, colour]
  · by_cases t : a < k <;> simp [colour, h, t]

theorem colour_test (k y : Fin n) : colour k y ≤ colour k k ↔ y ≤ k := by
  simp [colour]
  split_ifs <;> omega

def mark (s : Finset (Fin n)) (x i : Fin n) : Nat :=
  if i ∈ s then 0 else if i = x then 1 else 2

def markedWeight (gaps : List Nat) (s : Finset (Fin n)) (x : Fin n) : Nat :=
  (trace (mark s x) gaps).count 1

/-- Position of each input key, in strictly increasing rank order. -/
def positions (P : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map P.symm

theorem walk_of_list (s : Finset (Fin n)) (l : List (Fin n))
    (hd : l.Nodup) (hf : ∀ x ∈ l, x ∉ s) :
    Walk (unused n) (addPosition n) l.length s l := by
  induction l generalizing s with
  | nil => exact .nil _
  | cons x xs ih =>
    apply Walk.cons ((unused_spec n s x).mpr (hf x (by simp)))
    apply ih (insert x s) hd.of_cons
    intro y hy
    have hn := hf y (by simp [hy])
    have hne : y ≠ x := fun e => hd.not_mem (e ▸ hy)
    simpa [hne] using hn

theorem list_of_walk {s : Finset (Fin n)} {l : List (Fin n)} {k : Nat}
    (hw : Walk (unused n) (addPosition n) k s l) :
    l.length = k ∧ l.Nodup ∧ ∀ x ∈ l, x ∉ s := by
  induction hw with
  | nil => simp
  | @cons k s x xs hx ht ih =>
    obtain ⟨hlen, hd, hf⟩ := ih
    have hx' := (unused_spec n s x).mp hx
    have hxmem : x ∉ xs := fun hm => hf x hm (by simp [addPosition])
    refine ⟨by simp [hlen], List.nodup_cons.mpr ⟨hxmem, hd⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hm
    · exact hx'
    · exact fun h => hf y hm (Finset.mem_insert_of_mem h)

theorem positions_walk (P : Equiv.Perm (Fin n)) :
    Walk (unused n) (addPosition n) n ∅ (positions P) := by
  have h := walk_of_list (∅ : Finset (Fin n)) (positions P)
    ((List.nodup_finRange n).map P.symm.injective) (by simp)
  simpa [positions] using h

theorem positions_injective : Function.Injective (positions (n := n)) := by
  intro P Q h
  have he : P.symm = Q.symm := by
    apply Equiv.ext
    intro i
    have h' : List.ofFn (fun j => P.symm j) = List.ofFn (fun j => Q.symm j) := by
      simpa [List.ofFn_eq_map, positions] using h
    exact congrFun (List.ofFn_injective h') i
  exact Equiv.symm_bijective.injective he

theorem permutation_of_walk {l : List (Fin n)}
    (hw : Walk (unused n) (addPosition n) n ∅ l) : ∃! P, positions P = l := by
  obtain ⟨hlen, hd, _⟩ := list_of_walk hw
  let g : Fin n → Fin n := fun i => l.get (Fin.cast hlen.symm i)
  have hi : Function.Injective g := (List.nodup_iff_injective_get.mp hd).comp
    (Fin.cast_injective hlen.symm)
  let e := Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hi)
  have h : positions e.symm = l := by
    apply List.ext_getElem
    · simp [positions, hlen]
    · intro i hi₁ hi₂
      simp [positions, e, g]
  exact ⟨e.symm, h, fun q hq => positions_injective (hq.trans h.symm)⟩

theorem path_sum (P : Equiv.Perm (Fin n)) (gaps : List Nat)
    (s : Finset (Fin n)) (xs : List (Fin n))
    (cover : ∀ i, i ∈ s ∨ i ∈ xs)
    (low : ∀ i ∈ s, ∀ j ∈ xs, P i < P j)
    (sorted : xs.Pairwise (fun i j => P i < P j)) :
    walkCost (addPosition n) (markedWeight gaps) s xs =
      (xs.map fun j => (trace (fun i => P i) gaps).count (P j)).sum := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp sorted
    have mem : ∀ i, i ∈ s ↔ P i < P x := by
      intro i
      refine ⟨fun hi => low i hi x (by simp), ?_⟩
      intro hi
      rcases cover i with hs | hl
      · exact hs
      · rcases List.mem_cons.mp hl with rfl | h
        · exact (lt_irrefl _ hi).elim
        · exact (lt_asymm hi (head i h)).elim
    have proj : mark s x = colour (P x) ∘ P := by
      funext i
      simp [mark, colour, mem, Function.comp_apply]
    have edge : markedWeight gaps s x = (trace (fun i => P i) gaps).count (P x) := by
      unfold markedWeight
      rw [proj]
      convert trace_mark _ (colour_mono _) (P x) 1 (colour_one _) (colour_test _)
        (fun i => P i) gaps using 1
      generalize trace (fun i => P i) gaps = ts
      induction ts with
      | nil => rfl
      | cons a as ih => simp only [List.count_cons, beq_iff_eq, ih]
    have cv : ∀ i, i ∈ addPosition n s x ∨ i ∈ xs := by
      intro i
      have := cover i
      simpa [addPosition, or_left_comm, or_assoc] using this
    have lw : ∀ i ∈ addPosition n s x, ∀ j ∈ xs, P i < P j := by
      intro i hi j hj
      rcases Finset.mem_insert.mp hi with rfl | hs
      · exact head j hj
      · exact low i hs j (List.mem_cons_of_mem _ hj)
    simp [walkCost, edge, ih _ cv lw tail]

theorem trace_length_counts (l : List (Fin n)) :
    ((List.finRange n).map fun i => l.count i).sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons]
    rw [List.sum_map_add]
    rw [ih]
    congr 1
    rw [List.sum_map_eq_nsmul_single a]
    · simp
    · intro b hb _
      simp [Ne.symm hb]

theorem shell_path (P : Equiv.Perm (Fin n)) (gaps : List Nat) :
    walkCost (addPosition n) (markedWeight gaps) ∅ (positions P) =
      (trace (fun i => P i) gaps).length := by
  have hp : (positions P).Pairwise (fun i j => P i < P j) := by
    simpa [positions, List.pairwise_map] using List.pairwise_lt_finRange n
  rw [path_sum P gaps ∅ (positions P) (by
    intro i
    exact Or.inr ((Equiv.Perm.map_finRange_perm P.symm).mem_iff.mpr (List.mem_finRange i))) (by simp) hp]
  simpa [positions, List.map_map, Function.comp_def] using
    trace_length_counts (trace (fun i => P i) gaps)

noncomputable def shellMaximum (n : Nat) (gaps : List Nat) : Nat :=
  bellman (unused n) (addPosition n) (markedWeight gaps) n ∅

/-- The maximum is over actual executions on *all* rank permutations.
The second conjunct constructs an input attaining the Bellman value. -/
theorem shellMaximum_exact (gaps : List Nat) :
    (∀ P : Equiv.Perm (Fin n), (trace (fun i => P i) gaps).length ≤ shellMaximum n gaps) ∧
    ∃ P : Equiv.Perm (Fin n), (trace (fun i => P i) gaps).length = shellMaximum n gaps := by
  obtain ⟨upper, l, hw, he⟩ := subset_bellman_exact n (markedWeight gaps)
  constructor
  · intro P
    rw [← shell_path P gaps]
    exact upper _ (positions_walk P)
  · obtain ⟨P, hp, _⟩ := permutation_of_walk hw
    exact ⟨P, (shell_path P gaps).symm.trans (hp ▸ he)⟩

end ShellMinimax
