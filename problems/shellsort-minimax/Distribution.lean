import Charging
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace ShellMinimax
open Polynomial
variable {n : Nat}

/-- Continuations are listed with their positions in rank order. -/
noncomputable def paths : Nat → Finset (Fin n) → List (List (Fin n))
  | 0, _ => [[]]
  | k+1, s => (unused n s).flatMap fun x => (paths k (insert x s)).map (x :: ·)

theorem mem_paths {k : Nat} {s : Finset (Fin n)} {xs : List (Fin n)} :
    xs ∈ paths k s ↔ Walk (unused n) (addPosition n) k s xs := by
  induction k generalizing s xs with
  | zero =>
    constructor
    · simp only [paths,List.mem_singleton]
      rintro rfl
      exact .nil _
    · intro h
      cases h
      simp [paths]
  | succ k ih =>
    simp only [paths,List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨x,hx,ys,hy,rfl⟩
      exact .cons hx (ih.mp hy)
    · intro h
      cases h with
      | cons hx ht => exact ⟨_,hx,_,ih.mpr ht,rfl⟩

theorem nodup_paths (k : Nat) (s : Finset (Fin n)) : (paths k s).Nodup := by
  induction k generalizing s with
  | zero => simp [paths]
  | succ k ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro x _
      exact (ih _).map (fun _ _ e => (List.cons.inj e).2)
    · have hd : (unused n s).Nodup := Finset.nodup_toList _
      apply hd.imp
      intro a b ne x ha hb
      obtain ⟨ys,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨zs,_,e⟩ := List.mem_map.mp hb
      exact ne (List.cons.inj e).1.symm

noncomputable def distribution (w : Finset (Fin n) → Fin n → Nat) :
    Nat → Finset (Fin n) → Polynomial Nat
  | 0, _ => 1
  | k+1, s => ((unused n s).map fun x => X^(w s x) * distribution w k (insert x s)).sum

private theorem flat_sum {α β R : Type*} [AddCommMonoid R] (l : List α)
    (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem distribution_paths (w : Finset (Fin n) → Fin n → Nat) (k : Nat) (s : Finset (Fin n)) :
    distribution w k s = ((paths k s).map fun xs => (X : Polynomial Nat)^(walkCost (addPosition n) w s xs)).sum := by
  induction k generalizing s with
  | zero => simp [distribution, paths, walkCost]
  | succ k ih =>
    rw [distribution,paths,flat_sum]
    congr 1
    apply List.map_congr_left
    intro x _
    rw [ih, List.map_map]
    simp only [Function.comp_def,walkCost,pow_add]
    symm
    apply List.sum_map_mul_left

/-- The counting polynomial is the sum of one monomial per actual input. -/
theorem distribution_actual (H : List Nat) (pos : ∀ h ∈ H, 0 < h) :
    distribution (fun s (x : Fin n) => edgeWeight n H s x.val) n ∅ =
      ∑ P : Equiv.Perm (Fin n), (X : Polynomial Nat)^(Operational.trace (fun i => P i) H).length := by
  classical
  let l : List (Equiv.Perm (Fin n)) := Finset.univ.toList
  have he : (paths n (∅ : Finset (Fin n))).Perm (l.map positions) := by
    apply (List.perm_ext_iff_of_nodup (nodup_paths _ _) ((Finset.nodup_toList _).map positions_injective)).mpr
    intro xs
    constructor
    · intro hx
      obtain ⟨P,hp,_⟩ := permutation_of_walk (mem_paths.mp hx)
      exact List.mem_map.mpr ⟨P,by simp [l],hp⟩
    · intro hx
      obtain ⟨P,_,rfl⟩ := List.mem_map.mp hx
      exact mem_paths.mpr (positions_walk P)
  rw [distribution_paths, (he.map _).sum_eq, List.map_map]
  simp only [Function.comp_def, ← actual_threshold_path _ _ pos]
  simp [l]

end ShellMinimax
