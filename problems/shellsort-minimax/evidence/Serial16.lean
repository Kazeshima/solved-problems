import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Reflected17
run_cmd Lean.logInfo m!"begin_ms {← IO.monoMsNow}"
def p4 : List (Fin 17) := [7, 3, 16, 13, 10, 6, 2, 15, 12, 9, 5, 1, 14, 11, 8, 4, 0]
def p25 : List (Fin 17) := [2, 16, 8, 14, 6, 12, 4, 10, 1, 15, 7, 13, 5, 11, 3, 9, 0]
def p68 : List (Fin 17) := [8, 15, 4, 10, 14, 3, 9, 12, 16, 5, 2, 11, 0, 7, 13, 1, 6]
def p69 : List (Fin 17) := [8, 15, 4, 11, 7, 14, 3, 16, 5, 12, 2, 10, 0, 9, 6, 13, 1]
def p70 : List (Fin 17) := [14, 15, 5, 8, 12, 13, 4, 16, 6, 9, 0, 7, 2, 1, 10, 11, 3]
def p5 : List (Fin 17) := [13, 3, 10, 16, 8, 12, 2, 9, 15, 7, 11, 1, 6, 14, 5, 4, 0]
def p6 : List (Fin 17) := [13, 8, 14, 9, 16, 10, 5, 11, 6, 15, 2, 4, 7, 1, 12, 0, 3]
def p7 : List (Fin 17) := [6, 10, 11, 14, 16, 5, 9, 1, 12, 15, 4, 8, 0, 2, 13, 3, 7]
theorem mask256 : check (n := 17) 86 [10, 1] (.witness p4) = true := by decide
theorem mask257 : check (n := 17) 86 [10, 2, 1] (.witness p25) = true := by decide
theorem mask258 : check (n := 17) 86 [10, 3, 1] (.witness p68) = true := by decide
theorem mask259 : check (n := 17) 86 [10, 3, 2, 1] (.witness p68) = true := by decide
theorem mask260 : check (n := 17) 86 [10, 4, 1] (.witness p69) = true := by decide
theorem mask261 : check (n := 17) 86 [10, 4, 2, 1] (.witness p69) = true := by decide
theorem mask262 : check (n := 17) 86 [10, 4, 3, 1] (.witness p70) = true := by decide
theorem mask263 : check (n := 17) 86 [10, 4, 3, 2, 1] (.witness p70) = true := by decide
theorem mask264 : check (n := 17) 86 [10, 5, 1] (.witness p4) = true := by decide
theorem mask265 : check (n := 17) 86 [10, 5, 2, 1] (.witness p5) = true := by decide
theorem mask266 : check (n := 17) 86 [10, 5, 3, 1] (.witness p6) = true := by decide
theorem mask267 : check (n := 17) 86 [10, 5, 3, 2, 1] (.witness p6) = true := by decide
theorem mask268 : check (n := 17) 86 [10, 5, 4, 1] (.witness p7) = true := by decide
theorem mask269 : check (n := 17) 86 [10, 5, 4, 2, 1] (.witness p7) = true := by decide
theorem mask270 : check (n := 17) 86 [10, 5, 4, 3, 1] (.witness p70) = true := by decide
theorem mask271 : check (n := 17) 86 [10, 5, 4, 3, 2, 1] (.witness p70) = true := by decide
run_cmd Lean.logInfo m!"end_ms {← IO.monoMsNow}"
end ShellMinimax.Reflected17
