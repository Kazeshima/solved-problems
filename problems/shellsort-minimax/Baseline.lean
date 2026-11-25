import Geometry
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace ShellMinimax
open Operational
variable {n : Nat} {α : Type*} [LinearOrder α]

private theorem ins_pos (v : α) (y : α) (ys : List α) : 0 < (ins v (y::ys)).2 := by
  by_cases p : y ≤ v <;> simp [ins,p]

private theorem chain_lower (l : List α) : l.length ≤ (chain l).2.length + 1 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    cases as with
    | nil => simp [chain,ins]
    | cons b bs =>
      have hp : (chain (b::bs)).1 ≠ [] := by
        intro he
        have hlen := (List.perm_insertionSort (· ≥ ·) (b::bs)).length_eq
        rw [← chain_values, he] at hlen
        simp at hlen
      obtain ⟨y,ys,e⟩ := List.exists_cons_of_ne_nil hp
      have hc : 0 < (ins a (chain (b::bs)).1).2 := e ▸ ins_pos a y ys
      change (b::bs).length + 1 ≤ ((chain (b::bs)).2 ++ List.replicate (ins a (chain (b::bs)).1).2 a).length + 1
      simp only [List.length_append,List.length_replicate]
      omega

private theorem residue_partition (n h : Nat) (hh : 0 < h) :
    ((List.range h).flatMap (slots n h)).Perm (List.finRange n) := by
  have hd : ((List.range h).flatMap (slots n h)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun r _ => (List.nodup_finRange n).filter _, List.nodup_range.imp ?_⟩
    intro a b ne x ha hb
    simp [slots] at ha hb
    exact ne (ha.symm.trans hb)
  apply (List.perm_ext_iff_of_nodup hd (List.nodup_finRange n)).mpr
  intro x
  simp only [List.mem_flatMap,List.mem_range,slots,List.mem_filter,List.mem_finRange,true_and,
    beq_iff_eq,iff_true]
  exact ⟨x.val%h,Nat.mod_lt _ hh,rfl⟩

theorem pass_baseline (A : Fin n → α) (h : Nat) (hh : 0 < h) : n-h ≤ (passTrace A h).length := by
  have part := (residue_partition n h hh).length_eq
  rw [List.length_finRange] at part
  have aux (rs : List Nat) : (rs.flatMap (slots n h)).length ≤
      (rs.flatMap (fun r => (bucket A h r).2)).length + rs.length := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      have hr := chain_lower (((slots n h r).map A).reverse)
      simp only [List.length_reverse,List.length_map] at hr
      change (slots n h r).length ≤ (bucket A h r).2.length + 1 at hr
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  have v := aux (List.range h)
  rw [part,List.length_range] at v
  unfold passTrace
  omega

theorem baseline_le (A : Fin n → α) (H : List Nat) (pos : ∀ h ∈ H, 0 < h) :
    (H.map (n-·)).sum ≤ (trace A H).length := by
  induction H generalizing A with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.map_cons,List.sum_cons,trace,List.length_append]
    exact Nat.add_le_add (pass_baseline _ _ (pos h (by simp)))
      (ih _ (fun g hg => pos g (by simp [hg])))

end ShellMinimax
