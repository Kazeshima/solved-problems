import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples32 : List Line := signedLines% "38,71,96,0;36,71,98,0;35,71,101,1;33,71,103,1;61,71,105,0;60,71,106,0;59,71,109,0;58,71,110,0;54,71,113,1;53,71,114,1;51,71,116,1;48,71,119,1;1,72,74,0;4,72,76,0;5,72,78,0;11,72,81,0"
theorem valid32 : Valid false triples32 := by unfold Valid; decide +kernel
theorem distinct32 : Trace triples32 seen32 seen33 := by unfold Trace; decide +kernel
noncomputable def triples33 : List Line := signedLines% "8,72,82,0;15,72,85,0;12,72,86,0;54,72,88,0;55,72,90,0;52,72,93,1;53,72,95,1;59,72,96,0;57,72,99,1;62,72,100,0;60,72,103,1;32,72,104,0;33,72,106,0;38,72,109,0;39,72,111,0;43,72,113,0"
theorem valid33 : Valid false triples33 := by unfold Valid; decide +kernel
theorem distinct33 : Trace triples33 seen33 seen34 := by unfold Trace; decide +kernel
noncomputable def triples34 : List Line := signedLines% "40,72,114,0;46,72,117,0;45,72,118,0;1,73,75,0;4,73,77,0;5,73,79,0;11,73,80,1;8,73,83,0;15,73,84,1;12,73,87,0;54,73,89,0;55,73,91,0;52,73,92,0;53,73,94,0;59,73,97,0;57,73,98,0"
theorem valid34 : Valid false triples34 := by unfold Valid; decide +kernel
theorem distinct34 : Trace triples34 seen34 seen35 := by unfold Trace; decide +kernel
noncomputable def triples35 : List Line := signedLines% "62,73,101,0;60,73,102,0;32,73,105,0;33,73,107,0;38,73,108,1;39,73,110,1;43,73,112,1;40,73,115,0;46,73,116,1;45,73,119,0;5,74,76,0;4,74,78,0;10,74,80,1;9,74,83,1;14,74,84,1;13,74,87,1"
theorem valid35 : Valid false triples35 := by unfold Valid; decide +kernel
theorem distinct35 : Trace triples35 seen35 seen36 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
