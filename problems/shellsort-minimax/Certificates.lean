import Charging
import Baseline
import Mathlib.Data.Fintype.Powerset

namespace ShellMinimax.Certificate
open Operational

/-- Strict descent, membership of 1, and positive gaps below n.
In a descending list of positives, membership of 1 puts it last. -/
def Legal (n : Nat) (H : List Nat) : Prop :=
  H.Pairwise (· > ·) ∧ 1 ∈ H ∧ ∀ h ∈ H, 0 < h ∧ h < n

def tables (n : Nat) : Finset (Finset Nat) :=
  (Finset.range n).powerset.filter fun t => 1 ∈ t ∧ 0 ∉ t

def schedule (t : Finset Nat) := t.sort (· ≥ ·)

theorem enumeration {n : Nat} {H : List Nat} :
    Legal n H ↔ H.toFinset ∈ tables n ∧ schedule H.toFinset = H := by
  constructor
  · rintro ⟨order,last,bounds⟩
    constructor
    · simp only [tables,Finset.mem_filter,Finset.mem_powerset,List.mem_toFinset]
      exact ⟨fun h hh => Finset.mem_range.mpr (bounds h (List.mem_toFinset.mp hh)).2,
        last, fun h => Nat.lt_irrefl _ (bounds 0 h).1⟩
    · exact (List.toFinset_sort _ order.nodup).mpr (order.imp fun h => le_of_lt h)
  · rintro ⟨ht,hs⟩
    have ha := Finset.mem_filter.mp ht
    have hb := Finset.mem_powerset.mp ha.1
    refine ⟨hs ▸ Finset.sort_sorted_gt H.toFinset, List.mem_toFinset.mp ha.2.1, ?_⟩
    intro h hm
    have hl := List.mem_toFinset.mpr hm
    have hn : h ≠ 0 := fun e => ha.2.2 (e ▸ hl)
    exact ⟨Nat.pos_of_ne_zero hn,Finset.mem_range.mp (hb hl)⟩

theorem schedule_legal {n : Nat} {t : Finset Nat} (ht : t ∈ tables n) : Legal n (schedule t) := by
  apply enumeration.mpr
  simpa [schedule] using ht

def input {n : Nat} (a : List (Fin n)) (i : Fin n) := a.getD i.val i

def validInput {n : Nat} (a : List (Fin n)) : Bool :=
  decide (a.length = n ∧ ∀ i j : Fin n, input a i = input a j → i = j)

theorem input_perm {n : Nat} {a : List (Fin n)} (ha : validInput a = true) :
    ∃ P : Equiv.Perm (Fin n), ⇑P = input a := by
  have h := of_decide_eq_true ha
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp
    (show Function.Injective (input a) from fun i j e => h.2 i j e)),rfl⟩

def cost {n : Nat} (a : Fin n → Fin n) (H : List Nat) := (trace a H).length

def localCheck {n : Nat} (H : List Nat) (V : Finset (Fin n) → Nat) (s : Finset (Fin n)) : Bool :=
  decide (∀ x : Fin n, x ∉ s → edgeWeight n H s x.val + V (insert x s) ≤ V s)

/-- Certificates can partition these independent local checks however they like. -/
theorem potential_upper {n U : Nat} (H : List Nat) (V : Finset (Fin n) → Nat)
    (root : V ∅ ≤ U) (localOK : ∀ s, localCheck H V s = true) : thresholdMaximum n H ≤ U := by
  have bound {k s l} (w : Walk (unused n) (addPosition n) k s l) :
      walkCost (addPosition n) (fun s (x : Fin n) => edgeWeight n H s x.val) s l ≤ V s := by
    induction w with
    | nil => exact Nat.zero_le _
    | @cons k s x xs hx ht ih =>
      have he := of_decide_eq_true (localOK s) x ((unused_spec n s x).mp hx)
      exact (Nat.add_le_add_left ih _).trans he
  obtain ⟨_,l,hw,he⟩ := thresholdMaximum_exact n H
  exact he ▸ (bound hw).trans root

inductive Row (n : Nat) where
  | baseline
  | witness (a : List (Fin n))
  | optimum (a : List (Fin n)) (V : Finset (Fin n) → Nat)

def winner {n} : Row n → Bool
  | .optimum _ _ => true
  | _ => false

def check {n : Nat} (U : Nat) (H : List Nat) : Row n → Bool
  | .baseline => decide (U < (H.map (n-·)).sum)
  | .witness a => validInput a && decide (U < cost (input a) H)
  | .optimum a v => validInput a && decide (cost (input a) H = U) &&
      decide (v ∅ ≤ U) && decide (∀ s, localCheck H v s = true)

theorem row_sound {n U : Nat} {H : List Nat} (pos : ∀ h ∈ H, 0 < h) (r : Row n)
    (ok : check U H r = true) :
    if winner r then thresholdMaximum n H = U else U < thresholdMaximum n H := by
  have bound := (actual_threshold_maximum (n := n) H pos).1
  cases r with
  | baseline =>
    exact ((of_decide_eq_true ok).trans_le (baseline_le (id : Fin n → Fin n) H pos)).trans_le
      (bound (Equiv.refl _))
  | witness a =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨ha,hc⟩ := ok
    obtain ⟨P,hP⟩ := input_perm ha
    have hb := bound P
    rw [show (fun i => P i) = input a from hP] at hb
    exact hc.trans_le hb
  | optimum a V =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨⟨⟨ha,hc⟩,root⟩,localOK⟩ := ok
    obtain ⟨P,hP⟩ := input_perm ha
    have hb := bound P
    rw [show (fun i => P i) = input a from hP] at hb
    exact Nat.le_antisymm (potential_upper H V root localOK) (hc ▸ hb)

def tableGaps (n : Nat) (t : Finset Nat) := (List.range n).reverse.filter (· ∈ t)

theorem tableGaps_eq {n : Nat} {t : Finset Nat} (ht : t ∈ tables n) :
    tableGaps n t = schedule t := by
  have hb := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hrev : (List.range n).reverse.Pairwise (· > ·) := by
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range
  have hs : (tableGaps n t).Pairwise (· > ·) := hrev.sublist List.filter_sublist
  have ht' := Finset.sort_sorted_gt t
  apply List.eq_of_perm_of_sorted (r := (· ≥ ·)) _ (hs.imp fun h => le_of_lt h) (ht'.imp fun h => le_of_lt h)
  apply (List.perm_ext_iff_of_nodup hs.nodup ht'.nodup).mpr
  intro a
  simp only [tableGaps, List.mem_filter, List.mem_reverse, List.mem_range, decide_eq_true_eq,
    schedule, Finset.mem_sort]
  exact ⟨And.right, fun h => ⟨Finset.mem_range.mp (hb h),h⟩⟩

def checkAll (n U : Nat) (rows : Finset Nat → Row n) : Bool :=
  decide ((∃ t ∈ tables n, winner (rows t) = true) ∧
    ∀ t ∈ tables n, check U (tableGaps n t) (rows t) = true)

theorem certificate_sound {n U : Nat} {rows : Finset Nat → Row n}
    (hc : checkAll n U rows = true) :
    (∃ H, Legal n H ∧ thresholdMaximum n H = U) ∧
    ∀ H, Legal n H → U ≤ thresholdMaximum n H ∧
      (thresholdMaximum n H = U ↔ winner (rows H.toFinset) = true) := by
  obtain ⟨⟨t,ht,win⟩,raw⟩ := of_decide_eq_true hc
  have ok (t) (ht : t ∈ tables n) : check U (schedule t) (rows t) = true := tableGaps_eq ht ▸ raw t ht
  have hh := schedule_legal ht
  constructor
  · refine ⟨_,hh,?_⟩
    have he := row_sound (fun h hm => (hh.2.2 h hm).1) _ (ok t ht)
    simpa [win] using he
  · intro H hl
    obtain ⟨ht,hH⟩ := enumeration.mp hl
    have he := row_sound (fun h hm => (hl.2.2 h hm).1) (rows H.toFinset) (hH ▸ ok _ ht)
    cases e : winner (rows H.toFinset) <;> simp [e] at he ⊢ <;> omega

end ShellMinimax.Certificate
