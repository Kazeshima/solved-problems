import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples24 : List Line := signedLines% "47,66,88,0;46,66,91,1;45,66,92,0;44,66,95,1;34,66,96,0;32,66,98,0;39,66,101,0;37,66,103,0;57,66,105,0;56,66,106,0;63,66,109,1;62,66,110,1;50,66,113,1;49,66,114,1;55,66,116,0;52,66,119,0"
theorem valid24 : Valid false triples24 := by unfold Valid; decide +kernel
theorem distinct24 : Trace triples24 seen24 seen25 := by unfold Trace; decide +kernel
noncomputable def triples25 : List Line := signedLines% "6,67,69,0;4,67,71,0;25,67,72,1;24,67,75,0;29,67,76,1;28,67,79,0;18,67,80,0;17,67,83,1;22,67,84,0;21,67,87,1;47,67,89,0;46,67,90,0;45,67,93,0;44,67,94,0;34,67,97,0;32,67,99,0"
theorem valid25 : Valid false triples25 := by unfold Valid; decide +kernel
theorem distinct25 : Trace triples25 seen25 seen26 := by unfold Trace; decide +kernel
noncomputable def triples26 : List Line := signedLines% "39,67,100,1;37,67,102,1;57,67,104,1;56,67,107,0;63,67,108,0;62,67,111,1;50,67,112,0;49,67,115,1;55,67,117,0;52,67,118,1;2,68,70,0;31,68,72,0;30,68,75,1;27,68,76,0;26,68,79,1;20,68,80,0"
theorem valid26 : Valid false triples26 := by unfold Valid; decide +kernel
theorem distinct26 : Trace triples26 seen26 seen27 := by unfold Trace; decide +kernel
noncomputable def triples27 : List Line := signedLines% "23,68,83,0;16,68,84,0;19,68,87,0;41,68,89,0;40,68,90,0;43,68,93,0;42,68,94,0;36,68,97,1;38,68,99,1;33,68,100,1;35,68,102,1;63,68,105,1;62,68,106,1;57,68,109,0;56,68,110,0;52,68,113,1"
theorem valid27 : Valid false triples27 := by unfold Valid; decide +kernel
theorem distinct27 : Trace triples27 seen27 seen28 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
