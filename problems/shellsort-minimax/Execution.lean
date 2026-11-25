import Charging

namespace ShellMinimax
namespace Operational
variable {n : Nat} {α : Type*} [LinearOrder α]

/-- Run the ordinary insertion loop once per residue. Both the output array
and the comparison log read from the same materialized chain results. -/
def step (A : Fin n → α) (h : Nat) : (Fin n → α) × List α :=
  let columns := (List.range h).map (bucket A h)
  let output := fun i : Fin n =>
    let column := columns.getD (i.val%h) ([],[])
    column.1.reverse.getD (i.val/h) (A i)
  (output, columns.flatMap Prod.snd)

def execute (A : Fin n → α) : List Nat → (Fin n → α) × List α
  | [] => (A,[])
  | h :: hs =>
    let first := step A h
    let rest := execute first.1 hs
    (rest.1, first.2 ++ rest.2)

theorem step_output (A : Fin n → α) {h : Nat} (hh : 0 < h) : (step A h).1 = pass A h := by
  funext i
  have hi : i.val%h < ((List.range h).map (bucket A h)).length := by simp [Nat.mod_lt _ hh]
  simp only [step,pass]
  rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range]

theorem step_trace (A : Fin n → α) (h : Nat) : (step A h).2 = passTrace A h := by
  simp [step,passTrace,List.flatMap_map,Function.comp_def]

theorem execute_trace (A : Fin n → α) (H : List Nat) (pos : ∀ h ∈ H, 0 < h) :
    (execute A H).2 = trace A H := by
  induction H generalizing A with
  | nil => rfl
  | cons h hs ih =>
    simp only [execute,trace,step_trace,step_output _ (pos h (by simp)),
      ih _ (fun g hg => pos g (by simp [hg]))]

end Operational

/-- Exact, attained maximum of the program returning the sorted array and its
executed key-comparison trace. Every insertion call and residue result is shared. -/
theorem executed_maximum {n : Nat} (H : List Nat) (pos : ∀ h ∈ H, 0 < h) :
    (∀ P : Equiv.Perm (Fin n), (Operational.execute (fun i => P i) H).2.length ≤ thresholdMaximum n H) ∧
    ∃ P : Equiv.Perm (Fin n), (Operational.execute (fun i => P i) H).2.length = thresholdMaximum n H := by
  simpa only [Operational.execute_trace _ H pos] using actual_threshold_maximum (n := n) H pos

end ShellMinimax
