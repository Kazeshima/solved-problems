import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Reflected5
def values0 : Array Nat := #[10, 10, 9, 6, 8, 6, 5, 3, 7, 6, 5, 3, 4, 3, 2, 1, 6, 6, 5, 3, 4, 3, 2, 1, 3, 3, 2, 1, 1, 1, 0, 0]
def p0 : List (Fin 5) := [1, 3, 2, 4, 0]
def values2 : Array Nat := #[10, 9, 9, 8, 7, 6, 6, 5, 8, 5, 7, 4, 5, 3, 4, 2, 8, 7, 4, 4, 5, 4, 2, 2, 6, 3, 3, 1, 3, 1, 1, 0]
def p1 : List (Fin 5) := [1, 3, 4, 2, 0]
def p2 : List (Fin 5) := [1, 4, 3, 2, 0]
def values6 : Array Nat := #[10, 10, 9, 9, 7, 7, 6, 6, 9, 6, 7, 5, 6, 4, 4, 3, 9, 7, 8, 4, 6, 4, 5, 2, 5, 3, 4, 1, 3, 1, 2, 0]
def p3 : List (Fin 5) := [1, 2, 4, 3, 0]
def rows (t : Finset Nat) : Row 5 :=
  match t.sum (fun h => 2^h) with
  | 2 => .optimum [4, 3, 2, 1, 0] (fun s => values0[s.sum (fun i => 2^i.val)]?.getD 0)
  | 6 => .witness p0
  | 10 => .optimum [3, 1, 4, 2, 0] (fun s => values2[s.sum (fun i => 2^i.val)]?.getD 0)
  | 14 => .witness p1
  | 18 => .witness p2
  | 22 => .witness p2
  | 26 => .optimum [1, 2, 4, 3, 0] (fun s => values6[s.sum (fun i => 2^i.val)]?.getD 0)
  | 30 => .witness p3
  | _ => .baseline
theorem checked : checkAll 5 10 rows = true := by decide
def minimizers : List (List Nat) := [[1], [3, 1], [4, 3, 1]]
theorem names : ∀ t ∈ tables 5, winner (rows t) = true ↔ tableGaps 5 t ∈ minimizers := by decide
theorem global :
    (∃ H, Legal 5 H ∧ thresholdMaximum 5 H = 10) ∧
    ∀ H, Legal 5 H → 10 ≤ thresholdMaximum 5 H ∧
      (thresholdMaximum 5 H = 10 ↔ winner (rows H.toFinset) = true) :=
  certificate_sound checked
theorem exact_minimizers (H : List Nat) (hl : Legal 5 H) :
    thresholdMaximum 5 H = 10 ↔ H ∈ minimizers := by
  obtain ⟨ht,hH⟩ := enumeration.mp hl
  have hn := names H.toFinset ht
  rw [tableGaps_eq ht,hH] at hn
  exact (global.2 H hl).2.trans hn
end ShellMinimax.Reflected5
