import Geometry
import PermutationPaths

namespace ShellMinimax
open Operational

variable {n h : Nat}

private theorem nth_le (l : List Nat) (hs : l.Pairwise (· ≤ ·)) (i d k : Nat)
    (hi : i < l.length) :
    l.getD i d ≤ k ↔ i < (l.filter (· ≤ k)).length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp hs
    by_cases ha : a ≤ k
    · cases i with
      | zero => simp [ha]
      | succ i => simpa [ha] using ih tail i (by simpa using hi)
    · have empty : as.filter (· ≤ k) = [] := List.filter_eq_nil_iff.mpr (by
        intro b hb
        have := head b hb
        simp
        omega)
      cases i with
      | zero => simp [ha,empty]
      | succ i =>
        have ht := ih tail i (by simpa using hi)
        simp [empty] at ht
        simp [ha,empty,ht]

theorem pass_le (A : Fin n → Nat) (hh : 0 < h) (i : Fin n) (k : Nat) :
    pass A h i ≤ k ↔ i.val/h <
      ((slots n h (i.val%h)).filter fun j => decide (A j ≤ k)).length := by
  let l := (slots n h (i.val%h)).map A
  have perm : (bucket A h (i.val%h)).1.reverse.Perm l := by
    exact (List.reverse_perm _).trans ((by rw [bucket,chain_values]; exact List.perm_insertionSort _ _ : (bucket A h (i.val%h)).1.Perm l.reverse).trans (List.reverse_perm l))
  have sorted : (bucket A h (i.val%h)).1.reverse.Pairwise (· ≤ ·) := by
    rw [bucket,chain_values,List.pairwise_reverse]
    exact List.sorted_insertionSort _ _
  have hi : i.val/h < (bucket A h (i.val%h)).1.reverse.length := by
    rw [perm.length_eq]
    simpa [l,slots_length (Nat.mod_lt _ hh)] using index_lt_colLen i hh
  unfold pass
  rw [nth_le _ sorted _ _ _ hi, (perm.filter _).length_eq]
  simp [l,List.filter_map,Function.comp_def]

theorem count_insert (s : Finset (Fin n)) (x i : Fin n) (hx : x ∉ s) :
    chainCount n h (insert x s) i = chainCount n h s i +
      (if x.val%h = i.val%h then 1 else 0) := by
  unfold chainCount
  by_cases hr : x.val%h = i.val%h <;> simp [Finset.filter_insert,hr,hx]

theorem count_lt_colLen (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) :
    chainCount n h s x < colLen n h (x.val%h) := by
  have he := List.length_filter_le (fun i : Fin n => decide (i ∈ insert x s)) (slots n h (x.val%h))
  rw [full_count, slots_length (Nat.mod_lt _ hh)] at he
  change chainCount n h (insert x s) x ≤ _ at he
  simpa [count_insert s x x hx] using he

def transported (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) : Fin n :=
  coord n h (x.val%h) ⟨chainCount n h s x, count_lt_colLen s x hx hh⟩

theorem binaryPass_insert (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) :
    binaryPass n h (insert x s) = insert (transported s x hx hh) (binaryPass n h s) := by
  let z := transported s x hx hh
  have mz : z.val%h = x.val%h := coord_mod (Nat.mod_lt _ hh) _
  have dz : z.val/h = chainCount n h s x := coord_div (Nat.mod_lt _ hh) _
  ext i
  change i ∈ binaryPass n h (insert x s) ↔ i ∈ insert z (binaryPass n h s)
  simp only [binaryPass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [count_insert _ _ _ hx]
  by_cases hr : x.val%h = i.val%h
  · have hc : chainCount n h s x = chainCount n h s i := by simp [chainCount,hr]
    have hz : i = z ↔ i.val/h = chainCount n h s i := by
      constructor
      · rintro rfl
        exact dz.trans hc
      · intro hd
        apply Fin.ext
        have h1 := Nat.mod_add_div i.val h
        have h2 := Nat.mod_add_div z.val h
        rw [mz,hr,dz,hc,← hd] at h2
        omega
    rw [if_pos hr,hz]
    omega
  · have ne : i ≠ z := fun e => hr (e ▸ mz.symm)
    simp [hr,ne]

theorem transported_fresh (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) :
    transported s x hx hh ∉ binaryPass n h s := by
  let z := transported s x hx hh
  have mz : z.val%h = x.val%h := coord_mod (Nat.mod_lt _ hh) _
  have dz : z.val/h = chainCount n h s x := coord_div (Nat.mod_lt _ hh) _
  change z ∉ binaryPass n h s
  simp [binaryPass,dz,chainCount,mz]

theorem binaryPass_card (s : Finset (Fin n)) (hh : 0 < h) : (binaryPass n h s).card = s.card := by
  induction s using Finset.induction_on with
  | empty => simp [binaryPass,chainCount]
  | @insert x s hx ih => simp [binaryPass_insert s x hx hh, transported_fresh s x hx hh, hx, ih]

private theorem mark_le_zero (s : Finset (Fin n)) (x i : Fin n) :
    mark s x i ≤ 0 ↔ i ∈ s := by
  simp only [mark]
  split_ifs <;> simp_all

private theorem mark_le_one (s : Finset (Fin n)) (x i : Fin n) :
    mark s x i ≤ 1 ↔ i ∈ insert x s := by
  simp only [mark, Finset.mem_insert]
  split_ifs <;> simp_all

theorem pass_mark (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) :
    pass (mark s x) h = mark (binaryPass n h s) (transported s x hx hh) := by
  funext i
  have h0 := pass_le (mark s x) hh i 0
  have h1 := pass_le (mark s x) hh i 1
  simp only [mark_le_zero,full_count] at h0
  simp only [mark_le_one,full_count] at h1
  have zero : pass (mark s x) h i ≤ 0 ↔ i ∈ binaryPass n h s := by simpa [binaryPass,chainCount] using h0
  have one : pass (mark s x) h i ≤ 1 ↔ i = transported s x hx hh ∨ i ∈ binaryPass n h s := by
    rw [← Finset.mem_insert, ← binaryPass_insert s x hx hh]
    simpa [binaryPass,chainCount] using h1
  have two : pass (mark s x) h i ≤ 2 := by
    rw [pass_le _ hh]
    have ha (j : Fin n) : mark s x j ≤ 2 := by unfold mark; split_ifs <;> decide
    simpa [ha,slots_length (Nat.mod_lt _ hh)] using index_lt_colLen i hh
  change pass (mark s x) h i = (if i ∈ binaryPass n h s then 0 else if i = transported s x hx hh then 1 else 2)
  by_cases m : i ∈ binaryPass n h s
  · simp only [if_pos m]
    exact Nat.eq_zero_of_le_zero (zero.mpr m)
  · simp only [if_neg m]
    have nz := mt zero.mp m
    by_cases e : i = transported s x hx hh
    · have H := one.mpr (Or.inl e)
      simp only [if_pos e]
      omega
    · have H := mt one.mp (not_or_intro e m)
      simp only [if_neg e]
      omega

end ShellMinimax
