import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples40 : List Line := signedLines% "50,77,88,1;51,77,90,1;48,77,93,0;49,77,95,0;63,77,96,0;61,77,99,1;58,77,100,1;56,77,103,0;36,77,104,0;37,77,106,0;34,77,109,1;35,77,111,1;47,77,113,0;44,77,114,0;42,77,117,1;41,77,118,1"
theorem valid40 : Valid false triples40 := by unfold Valid; decide +kernel
theorem distinct40 : Trace triples40 seen40 seen41 := by unfold Trace; decide +kernel
noncomputable def triples41 : List Line := signedLines% "14,78,80,1;13,78,83,1;10,78,84,1;9,78,87,1;51,78,89,0;50,78,91,0;49,78,92,0;48,78,94,0;62,78,96,0;60,78,99,1;59,78,100,0;57,78,103,1;37,78,105,1;36,78,107,1;35,78,108,1;34,78,110,1"
theorem valid41 : Valid false triples41 := by unfold Valid; decide +kernel
theorem distinct41 : Trace triples41 seen41 seen42 := by unfold Trace; decide +kernel
noncomputable def triples42 : List Line := signedLines% "46,78,113,0;45,78,114,1;43,78,117,0;40,78,118,1;14,79,81,1;13,79,82,0;10,79,85,1;9,79,86,0;51,79,88,1;50,79,90,1;49,79,93,0;48,79,95,0;62,79,97,0;60,79,98,0;59,79,101,0;57,79,102,0"
theorem valid42 : Valid false triples42 := by unfold Valid; decide +kernel
theorem distinct42 : Trace triples42 seen42 seen43 := by unfold Trace; decide +kernel
noncomputable def triples43 : List Line := signedLines% "37,79,104,0;36,79,106,0;35,79,109,1;34,79,111,1;46,79,112,1;45,79,115,1;43,79,116,1;40,79,119,1;3,80,82,0;4,80,84,0;7,80,86,0;61,80,88,0;60,80,91,1;63,80,93,0;62,80,94,0;48,80,96,0"
theorem valid43 : Valid false triples43 := by unfold Valid; decide +kernel
theorem distinct43 : Trace triples43 seen43 seen44 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
