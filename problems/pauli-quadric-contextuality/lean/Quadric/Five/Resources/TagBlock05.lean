import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples20 : List Line := signedLines% "2,64,66,0;4,64,68,0;6,64,70,0;27,64,72,0;26,64,75,1;31,64,76,0;30,64,79,1;16,64,80,0;19,64,83,0;20,64,84,0;23,64,87,0;45,64,88,0;44,64,91,1;47,64,92,0;46,64,95,1;32,64,96,0"
theorem valid20 : Valid false triples20 := by unfold Valid; decide +kernel
theorem distinct20 : Trace triples20 seen20 seen21 := by unfold Trace; decide +kernel
noncomputable def triples21 : List Line := signedLines% "34,64,98,0;37,64,101,0;39,64,103,0;59,64,104,0;58,64,107,1;61,64,108,0;60,64,111,1;48,64,112,0;51,64,115,0;53,64,117,0;54,64,118,0;2,65,67,0;4,65,69,0;6,65,71,0;27,65,73,0;26,65,74,0"
theorem valid21 : Valid false triples21 := by unfold Valid; decide +kernel
theorem distinct21 : Trace triples21 seen21 seen22 := by unfold Trace; decide +kernel
noncomputable def triples22 : List Line := signedLines% "31,65,77,0;30,65,78,0;16,65,81,0;19,65,82,1;20,65,85,0;23,65,86,1;45,65,89,0;44,65,90,0;47,65,93,0;46,65,94,0;32,65,97,0;34,65,99,0;37,65,100,1;39,65,102,1;59,65,105,0;58,65,106,0"
theorem valid22 : Valid false triples22 := by unfold Valid; decide +kernel
theorem distinct22 : Trace triples22 seen22 seen23 := by unfold Trace; decide +kernel
noncomputable def triples23 : List Line := signedLines% "61,65,109,0;60,65,110,0;48,65,113,0;51,65,114,1;53,65,116,1;54,65,119,0;6,66,68,0;4,66,70,0;25,66,73,0;24,66,74,0;29,66,77,0;28,66,78,0;18,66,81,1;17,66,82,1;22,66,85,1;21,66,86,1"
theorem valid23 : Valid false triples23 := by unfold Valid; decide +kernel
theorem distinct23 : Trace triples23 seen23 seen24 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
