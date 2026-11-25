import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Witnesses

def w17_9 : List (Fin 17) := [9, 13, 4, 14, 11, 15, 7, 12, 16, 8, 0, 3, 2, 10, 1, 6, 5]
theorem w17_9_checked : validInput w17_9 = true ∧ cost (input w17_9) [9, 6, 4, 1] = 86 := by decide
theorem w17_9_attains : ∃ P : Equiv.Perm (Fin 17), cost P [9, 6, 4, 1] = 86 := by
  obtain ⟨P,hP⟩ := input_perm w17_9_checked.1
  exact ⟨P, hP ▸ w17_9_checked.2⟩

def w18_17 : List (Fin 18) := [6, 0, 8, 2, 10, 1, 16, 3, 4, 7, 15, 9, 14, 11, 12, 17, 13, 5]
theorem w18_17_checked : validInput w18_17 = true ∧ cost (input w18_17) [17, 9, 6, 4, 1] = 94 := by decide
theorem w18_17_attains : ∃ P : Equiv.Perm (Fin 18), cost P [17, 9, 6, 4, 1] = 94 := by
  obtain ⟨P,hP⟩ := input_perm w18_17_checked.1
  exact ⟨P, hP ▸ w18_17_checked.2⟩

def w19_9 : List (Fin 19) := [13, 6, 15, 18, 8, 14, 12, 17, 4, 10, 5, 0, 2, 7, 11, 1, 16, 3, 9]
theorem w19_9_checked : validInput w19_9 = true ∧ cost (input w19_9) [9, 7, 4, 1] = 103 := by decide
theorem w19_9_attains : ∃ P : Equiv.Perm (Fin 19), cost P [9, 7, 4, 1] = 103 := by
  obtain ⟨P,hP⟩ := input_perm w19_9_checked.1
  exact ⟨P, hP ▸ w19_9_checked.2⟩

def w20_11 : List (Fin 20) := [15, 7, 16, 10, 3, 13, 18, 14, 8, 19, 6, 4, 0, 12, 2, 1, 9, 17, 11, 5]
theorem w20_11_checked : validInput w20_11 = true ∧ cost (input w20_11) [11, 7, 5, 1] = 112 := by decide
theorem w20_11_attains : ∃ P : Equiv.Perm (Fin 20), cost P [11, 7, 5, 1] = 112 := by
  obtain ⟨P,hP⟩ := input_perm w20_11_checked.1
  exact ⟨P, hP ▸ w20_11_checked.2⟩

def w21_9 : List (Fin 21) := [19, 7, 9, 10, 17, 20, 14, 12, 4, 18, 6, 8, 2, 15, 13, 1, 11, 3, 16, 5, 0]
theorem w21_9_checked : validInput w21_9 = true ∧ cost (input w21_9) [9, 7, 4, 1] = 121 := by decide
theorem w21_9_attains : ∃ P : Equiv.Perm (Fin 21), cost P [9, 7, 4, 1] = 121 := by
  obtain ⟨P,hP⟩ := input_perm w21_9_checked.1
  exact ⟨P, hP ▸ w21_9_checked.2⟩

def w21_20 : List (Fin 21) := [6, 12, 7, 2, 1, 10, 8, 3, 19, 5, 16, 9, 18, 14, 11, 17, 15, 20, 4, 13, 0]
theorem w21_20_checked : validInput w21_20 = true ∧ cost (input w21_20) [20, 9, 7, 4, 1] = 121 := by decide
theorem w21_20_attains : ∃ P : Equiv.Perm (Fin 21), cost P [20, 9, 7, 4, 1] = 121 := by
  obtain ⟨P,hP⟩ := input_perm w21_20_checked.1
  exact ⟨P, hP ▸ w21_20_checked.2⟩

end ShellMinimax.Witnesses
