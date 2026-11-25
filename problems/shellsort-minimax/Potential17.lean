import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace ShellMinimax.Block17
def localValues (s : Finset (Fin 17)) : Nat :=
  match s.sum (fun i => 2^i.val) with
  | 0 => 86
  | 1 => 86
  | 2 => 85
  | 3 => 82
  | 4 => 84
  | 5 => 83
  | 6 => 81
  | 7 => 79
  | 8 => 83
  | 9 => 83
  | 10 => 82
  | 11 => 79
  | 12 => 81
  | 13 => 81
  | 14 => 78
  | 15 => 76
  | 16 => 85
  | 17 => 81
  | 18 => 83
  | 19 => 78
  | 20 => 82
  | 21 => 78
  | 22 => 79
  | 23 => 74
  | 32 => 84
  | 33 => 81
  | 34 => 79
  | 35 => 77
  | 36 => 81
  | 37 => 80
  | 38 => 76
  | 39 => 75
  | 64 => 85
  | 65 => 81
  | 66 => 82
  | 67 => 77
  | 68 => 82
  | 69 => 76
  | 70 => 78
  | 71 => 73
  | 128 => 84
  | 129 => 81
  | 130 => 80
  | 131 => 77
  | 132 => 81
  | 133 => 79
  | 134 => 76
  | 135 => 74
  | 256 => 83
  | 257 => 82
  | 258 => 80
  | 259 => 78
  | 260 => 80
  | 261 => 77
  | 262 => 76
  | 263 => 73
  | 512 => 85
  | 513 => 79
  | 514 => 81
  | 515 => 77
  | 516 => 82
  | 517 => 77
  | 518 => 78
  | 519 => 74
  | 1024 => 84
  | 1025 => 81
  | 1026 => 78
  | 1027 => 75
  | 1028 => 80
  | 1029 => 78
  | 1030 => 77
  | 1031 => 72
  | 2048 => 83
  | 2049 => 82
  | 2050 => 80
  | 2051 => 78
  | 2052 => 78
  | 2053 => 75
  | 2054 => 74
  | 2055 => 71
  | 4096 => 82
  | 4097 => 82
  | 4098 => 81
  | 4099 => 78
  | 4100 => 80
  | 4101 => 80
  | 4102 => 77
  | 4103 => 75
  | 8192 => 84
  | 8193 => 80
  | 8194 => 82
  | 8195 => 77
  | 8196 => 81
  | 8197 => 77
  | 8198 => 78
  | 8199 => 73
  | 16384 => 83
  | 16385 => 80
  | 16386 => 78
  | 16387 => 76
  | 16388 => 80
  | 16389 => 79
  | 16390 => 75
  | 16391 => 74
  | 32768 => 84
  | 32769 => 80
  | 32770 => 81
  | 32771 => 76
  | 32772 => 81
  | 32773 => 75
  | 32774 => 77
  | 32775 => 72
  | 65536 => 83
  | 65537 => 80
  | 65538 => 79
  | 65539 => 76
  | 65540 => 80
  | 65541 => 78
  | 65542 => 75
  | 65543 => 73
  | _ => 0
theorem state0 : localCheck [9, 6, 4, 1] localValues ∅ = true := by decide
theorem state1 : localCheck [9, 6, 4, 1] localValues {0} = true := by decide
theorem state2 : localCheck [9, 6, 4, 1] localValues {1} = true := by decide
theorem state3 : localCheck [9, 6, 4, 1] localValues {0,1} = true := by decide
theorem state4 : localCheck [9, 6, 4, 1] localValues {2} = true := by decide
theorem state5 : localCheck [9, 6, 4, 1] localValues {0,2} = true := by decide
theorem state6 : localCheck [9, 6, 4, 1] localValues {1,2} = true := by decide
theorem state7 : localCheck [9, 6, 4, 1] localValues {0,1,2} = true := by decide
end ShellMinimax.Block17
