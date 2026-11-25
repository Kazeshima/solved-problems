import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Reflected17
def p0 : List (Fin 17) := [9, 13, 4, 14, 11, 15, 7, 12, 16, 8, 0, 3, 2, 10, 1, 6, 5]
def p1 : List (Fin 17) := [11, 5, 16, 10, 4, 15, 9, 3, 14, 8, 2, 13, 7, 1, 12, 6, 0]
def p2 : List (Fin 17) := [4, 16, 12, 8, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5, 0]
def p3 : List (Fin 17) := [7, 9, 14, 16, 6, 8, 11, 15, 3, 5, 10, 13, 2, 4, 1, 12, 0]
theorem mask0 : check (n := 17) 86 [1] (.witness p0) = true := by decide
theorem mask1 : check (n := 17) 86 [2, 1] (.witness p0) = true := by decide
theorem mask2 : check (n := 17) 86 [3, 1] (.witness p1) = true := by decide
theorem mask3 : check (n := 17) 86 [3, 2, 1] (.witness p1) = true := by decide
theorem mask4 : check (n := 17) 86 [4, 1] (.witness p2) = true := by decide
theorem mask5 : check (n := 17) 86 [4, 2, 1] (.witness p2) = true := by decide
theorem mask6 : check (n := 17) 86 [4, 3, 1] (.witness p3) = true := by decide
theorem mask7 : check (n := 17) 86 [4, 3, 2, 1] (.witness p3) = true := by decide
end ShellMinimax.Reflected17
