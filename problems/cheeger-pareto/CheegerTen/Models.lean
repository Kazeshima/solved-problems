import CheegerPareto
import Mathlib.Tactic.FinCases

/-! Exact certificates for the three surviving graph6 records of order ten. -/
namespace CheegerPareto.Ten

open scoped BigOperators
abbrev Model := Fin 3

private def ordinary : EdgeSet 10 :=
  {(0,3),(0,6),(3,6), (1,4),(1,7),(4,7), (2,5),(2,8),(5,8), (0,7),(0,8),(7,8)}

def edgesOf (i : Model) : EdgeSet 10 :=
  ordinary ∪ (if i = 0 then {(0,9),(1,9),(2,9),(3,9),(7,9),(8,9)}
    else if i = 1 then {(0,9),(1,9),(2,9),(3,9),(5,9),(7,9)}
    else {(0,9),(1,9),(2,9),(3,9),(4,9),(5,9),(6,9),(7,9),(8,9)})

def code (i : Model) := if i = 0 then "ICOceQd{W" else if i = 1 then "ICOceQd|O" else "ICOceQd~w"
def mass (i : Model) : ℕ := if i = 2 then 8 else 6
def numerator (i : Model) : ℕ := if i = 2 then 5 else 4
noncomputable def weight (i : Model) (v : V) : ℝ := if v = 9 then mass i else 0
def row : Finset V := {0,3,6}
def tightSets : Finset (Finset V) := {{0,3,6,9}, {1,4,7,9}, {2,5,8,9}}

private def words (i : Model) := (code i).toList.map (fun c => c.toNat - 63)
private def bit (i : Model) (pos : ℕ) :=
  ((words i).getD (1 + pos / 6) 0).testBit (5 - pos % 6)

theorem graph6_identities (i : Model) :
    (words i).head? = some 10 ∧ (words i).length = 9 ∧
    (∀ j : Fin 3, bit i (45 + j.val) = false) ∧
    ∀ u v : V, (u,v) ∈ edgesOf i ↔
      u < v ∧ bit i (v.val * (v.val - 1) / 2 + u.val) = true := by
  fin_cases i <;> decide +kernel

theorem ordered (i : Model) : OrderedEdges (edgesOf i) := by
  unfold OrderedEdges
  fin_cases i <;> decide +kernel

theorem edge_counts (i : Model) : (edgesOf i).card = if i = 2 then 21 else 18 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem small_cuts (i : Model) : ∀ s : Finset V, s.card ≤ 5 →
    numerator i * s.card ≤ 3 * cutSize (edgesOf i) s ∧
      ((9 : V) ∈ s → mass i ≤ cutSize (edgesOf i) s) := by
  fin_cases i <;> decide +kernel

theorem attainment (i : Model) : row.card = 3 ∧ cutSize (edgesOf i) row = numerator i := by
  fin_cases i <;> decide +kernel

theorem covering (i : Model) : ∀ v : V, ∃ s ∈ tightSets, v ∈ s ∧
    (9 : V) ∈ s ∧ s.card ≤ 5 ∧ cutSize (edgesOf i) s = mass i := by
  fin_cases i <;> decide +kernel

end CheegerPareto.Ten
