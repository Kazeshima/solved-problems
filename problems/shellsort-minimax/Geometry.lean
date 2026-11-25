import Operational
import BooleanLattice
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Push

namespace ShellMinimax
open Operational
variable {n h : Nat}

/-- Number of physical slots in residue r, including a possible short last row. -/
def colLen (n h r : Nat) := if r < n then (n-1-r)/h+1 else 0

def coord (n h r : Nat) (j : Fin (colLen n h r)) : Fin n :=
  ⟨r + h*j.val, by
    have hj := j.isLt
    by_cases hr : r < n
    · simp [colLen,hr] at hj
      have hm := Nat.mul_le_mul_left h (show j.val ≤ (n-1-r)/h by omega)
      have ht := Nat.mul_div_le (n-1-r) h
      omega
    · simp [colLen,hr] at hj⟩

theorem coord_mod (hr : r < h) (j : Fin (colLen n h r)) :
    (coord n h r j).val % h = r := by simp [coord, Nat.add_mod, Nat.mod_eq_of_lt hr]

theorem coord_div (hr : r < h) (j : Fin (colLen n h r)) :
    (coord n h r j).val / h = j.val := by
  have hh : 0 < h := by omega
  simp [coord, Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hr]

theorem index_lt_colLen (x : Fin n) (hh : 0 < h) :
    x.val / h < colLen n h (x.val % h) := by
  have hv := x.isLt
  have he := Nat.mod_add_div x.val h
  have hr := Nat.mod_le x.val h
  rw [colLen, if_pos (by omega)]
  apply Nat.lt_succ_of_le
  apply (Nat.le_div_iff_mul_le hh).mpr
  rw [Nat.mul_comm]
  omega

theorem slots_eq (hr : r < h) :
    slots n h r = List.ofFn (coord n h r) := by
  have hh : 0 < h := by omega
  have hm (x : Fin n) : x ∈ List.ofFn (coord n h r) ↔ x.val % h = r := by
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨j,rfl⟩
      exact coord_mod hr _
    · rintro rfl
      exact ⟨⟨x.val/h, index_lt_colLen x hh⟩, Fin.ext (Nat.mod_add_div _ _)⟩
  have hl : (slots n h r).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n).sublist List.filter_sublist
  have hs : (List.ofFn (coord n h r)).Pairwise (· < ·) := by
    rw [List.ofFn_eq_map, List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun {i j} ij =>
      show r + h*i.val < r + h*j.val from Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left ij hh) r
  exact List.eq_of_perm_of_sorted
    ((List.perm_ext_iff_of_nodup hl.nodup hs.nodup).mpr (fun x => by simp [slots, hm])) hl hs

theorem slots_length (hr : r < h) : (slots n h r).length = colLen n h r := by
  simp [slots_eq hr]

private theorem range_before (a b : Nat) :
    ((List.range b).filter (· < a)).length = min a b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases lt : b < a <;> simp [lt] <;> omega

theorem slots_earlier (x : Fin n) (hh : 0 < h) :
    ((slots n h (x.val % h)).filter (· < x)).length = x.val/h := by
  let r := x.val % h
  have hr := Nat.mod_lt x.val hh
  have hi := index_lt_colLen x hh
  rw [slots_eq hr, List.ofFn_eq_map, List.filter_map, List.length_map]
  have htest (j : Fin (colLen n h r)) : coord n h r j < x ↔ j.val < x.val/h := by
    change r + h*j.val < x.val ↔ _
    have he := Nat.mod_add_div x.val h
    constructor
    · intro hj
      by_contra! hn
      have := Nat.mul_le_mul_left h hn
      dsimp [r] at *
      omega
    · intro hj
      have := Nat.mul_lt_mul_of_pos_left hj hh
      dsimp [r] at *
      omega
  change ((List.finRange (colLen n h r)).filter (fun j => decide (coord n h r j < x))).length = _
  simp only [htest]
  have hc : ((List.finRange (colLen n h r)).filter (fun i => decide (i.val < x.val/h))).length =
      ((List.range (colLen n h r)).filter (· < x.val/h)).length := by
    rw [← List.map_coe_finRange]
    rw [List.filter_map, List.length_map]
    rfl
  rw [hc, range_before, min_eq_left (Nat.le_of_lt hi)]

theorem selected_length (r : Nat) (p : Fin n → Prop) [DecidablePred p] :
    ((slots n h r).filter (fun i => decide (p i))).length =
      (Finset.univ.filter (fun i : Fin n => p i ∧ i.val % h = r)).card := by
  let l := (slots n h r).filter (fun i => decide (p i))
  have hd : l.Nodup := ((List.nodup_finRange n).filter _).filter _
  have he : l.toFinset = Finset.univ.filter (fun i : Fin n => p i ∧ i.val % h = r) := by
    ext i
    simp [l,slots,and_comm]
  rw [← he, List.toFinset_card_of_nodup hd]

theorem full_count (s : Finset (Fin n)) (r : Nat) :
    ((slots n h r).filter (· ∈ s)).length = (s.filter fun i => i.val % h = r).card := by
  rw [selected_length]
  congr 1
  ext
  simp

theorem count_before (s : Finset (Fin n)) (x : Fin n) :
    ((slots n h (x.val % h)).filter (fun i => decide (i < x ∧ i ∈ s))).length =
      earlierSmall n h s x.val := by
  rw [selected_length]
  unfold earlierSmall
  congr 1
  ext
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  tauto

end ShellMinimax
