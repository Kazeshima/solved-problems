import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples8 : List Line := signedLines% "11,19,24,0;11,21,30,1;11,23,28,0;11,32,43,0;11,34,41,0;11,36,47,0;11,38,45,0;11,49,58,1;11,51,56,0;11,53,62,1;11,55,60,0;12,16,28,0;12,18,30,0;12,20,24,0;12,22,26,0;12,33,45,0"
theorem valid8 : Valid true triples8 := by unfold Valid; decide +kernel
theorem distinct8 : Trace triples8 seen8 seen9 := by unfold Trace; decide +kernel
noncomputable def triples9 : List Line := signedLines% "12,35,47,0;12,37,41,1;12,39,43,1;12,49,61,0;12,51,63,0;12,53,57,1;12,55,59,1;13,16,29,0;13,18,31,0;13,20,25,0;13,22,27,0;13,33,44,1;13,35,46,1;13,37,40,0;13,39,42,0;13,49,60,1"
theorem valid9 : Valid true triples9 := by unfold Valid; decide +kernel
theorem distinct9 : Trace triples9 seen9 seen10 := by unfold Trace; decide +kernel
noncomputable def triples10 : List Line := signedLines% "13,51,62,1;13,53,56,0;13,55,58,0;14,17,31,0;14,19,29,1;14,21,27,0;14,23,25,1;14,33,47,0;14,35,45,0;14,37,43,1;14,39,41,1;14,48,62,1;14,50,60,0;14,52,58,0;14,54,56,1;15,17,30,1"
theorem valid10 : Valid true triples10 := by unfold Valid; decide +kernel
theorem distinct10 : Trace triples10 seen10 seen11 := by unfold Trace; decide +kernel
noncomputable def triples11 : List Line := signedLines% "15,19,28,0;15,21,26,1;15,23,24,0;15,33,46,1;15,35,44,1;15,37,42,0;15,39,40,0;15,48,63,1;15,50,61,0;15,52,59,0;15,54,57,1;16,32,48,0;16,33,49,0;16,36,52,0;16,37,53,0;16,40,56,0"
theorem valid11 : Valid true triples11 := by unfold Valid; decide +kernel
theorem distinct11 : Trace triples11 seen11 seen12 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
