import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Witnesses

def w22_5 : List (Fin 22) := [18, 13, 19, 14, 21, 15, 8, 16, 9, 20, 10, 5, 11, 6, 17, 2, 4, 7, 1, 12, 0, 3]
theorem w22_5_checked : validInput w22_5 = true ∧ cost (input w22_5) [5, 3, 1] = 131 := by decide
theorem w22_5_attains : ∃ P : Equiv.Perm (Fin 22), cost P [5, 3, 1] = 131 := by
  obtain ⟨P,hP⟩ := input_perm w22_5_checked.1
  exact ⟨P, hP ▸ w22_5_checked.2⟩

def w22_7 : List (Fin 22) := [17, 14, 19, 18, 4, 21, 13, 11, 10, 12, 15, 3, 20, 9, 7, 5, 8, 2, 1, 16, 6, 0]
theorem w22_7_checked : validInput w22_7 = true ∧ cost (input w22_7) [7, 5, 4, 1] = 131 := by decide
theorem w22_7_attains : ∃ P : Equiv.Perm (Fin 22), cost P [7, 5, 4, 1] = 131 := by
  obtain ⟨P,hP⟩ := input_perm w22_7_checked.1
  exact ⟨P, hP ▸ w22_7_checked.2⟩

def w22_8 : List (Fin 22) := [19, 21, 17, 5, 13, 11, 2, 15, 18, 20, 10, 4, 8, 9, 1, 14, 16, 12, 7, 0, 6, 3]
theorem w22_8_checked : validInput w22_8 = true ∧ cost (input w22_8) [8, 7, 3, 1] = 131 := by decide
theorem w22_8_attains : ∃ P : Equiv.Perm (Fin 22), cost P [8, 7, 3, 1] = 131 := by
  obtain ⟨P,hP⟩ := input_perm w22_8_checked.1
  exact ⟨P, hP ▸ w22_8_checked.2⟩

def w22_9 : List (Fin 22) := [21, 5, 17, 13, 19, 14, 8, 18, 16, 20, 4, 9, 7, 12, 10, 1, 15, 11, 6, 3, 0, 2]
theorem w22_9_checked : validInput w22_9 = true ∧ cost (input w22_9) [9, 7, 4, 1] = 131 := by decide
theorem w22_9_attains : ∃ P : Equiv.Perm (Fin 22), cost P [9, 7, 4, 1] = 131 := by
  obtain ⟨P,hP⟩ := input_perm w22_9_checked.1
  exact ⟨P, hP ▸ w22_9_checked.2⟩

def w22_21 : List (Fin 22) := [3, 10, 14, 2, 6, 8, 1, 19, 15, 17, 20, 5, 11, 9, 12, 21, 13, 16, 18, 4, 7, 0]
theorem w22_21_checked : validInput w22_21 = true ∧ cost (input w22_21) [21, 8, 7, 3, 1] = 131 := by decide
theorem w22_21_attains : ∃ P : Equiv.Perm (Fin 22), cost P [21, 8, 7, 3, 1] = 131 := by
  obtain ⟨P,hP⟩ := input_perm w22_21_checked.1
  exact ⟨P, hP ▸ w22_21_checked.2⟩

def w23_9 : List (Fin 23) := [15, 11, 21, 16, 14, 19, 17, 22, 4, 10, 6, 18, 12, 8, 13, 1, 20, 3, 9, 5, 0, 2, 7]
theorem w23_9_checked : validInput w23_9 = true ∧ cost (input w23_9) [9, 7, 4, 1] = 139 := by decide
theorem w23_9_attains : ∃ P : Equiv.Perm (Fin 23), cost P [9, 7, 4, 1] = 139 := by
  obtain ⟨P,hP⟩ := input_perm w23_9_checked.1
  exact ⟨P, hP ▸ w23_9_checked.2⟩

def w23_22 : List (Fin 23) := [6, 0, 18, 7, 9, 1, 17, 15, 5, 12, 4, 21, 13, 10, 14, 19, 22, 16, 11, 2, 20, 8, 3]
theorem w23_22_checked : validInput w23_22 = true ∧ cost (input w23_22) [22, 9, 7, 4, 1] = 139 := by decide
theorem w23_22_attains : ∃ P : Equiv.Perm (Fin 23), cost P [22, 9, 7, 4, 1] = 139 := by
  obtain ⟨P,hP⟩ := input_perm w23_22_checked.1
  exact ⟨P, hP ▸ w23_22_checked.2⟩

end ShellMinimax.Witnesses
