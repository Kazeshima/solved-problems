import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples4 : List Line := signedLines% "5,57,60,0;5,58,63,1;5,59,62,0;6,8,14,0;6,9,15,0;6,10,12,0;6,11,13,0;6,48,54,1;6,49,55,1;6,50,52,0;6,51,53,0;6,56,62,1;6,57,63,1;6,58,60,0;6,59,61,0;7,24,31,1"
theorem valid4 : Valid true triples4 := by unfold Valid; decide +kernel
theorem distinct4 : Trace triples4 seen4 seen5 := by unfold Trace; decide +kernel
noncomputable def triples5 : List Line := signedLines% "7,25,30,0;7,26,29,0;7,27,28,1;7,40,47,1;7,41,46,0;7,42,45,1;7,43,44,0;7,48,55,1;7,49,54,1;7,50,53,0;7,51,52,0;8,16,24,0;8,18,26,0;8,20,28,0;8,22,30,0;8,32,40,0"
theorem valid5 : Valid true triples5 := by unfold Valid; decide +kernel
theorem distinct5 : Trace triples5 seen5 seen6 := by unfold Trace; decide +kernel
noncomputable def triples6 : List Line := signedLines% "8,34,42,0;8,36,44,0;8,38,46,0;8,48,56,0;8,50,58,0;8,52,60,0;8,54,62,0;9,16,25,0;9,18,27,0;9,20,29,0;9,22,31,0;9,32,41,0;9,34,43,0;9,36,45,0;9,38,47,0;9,48,57,0"
theorem valid6 : Valid true triples6 := by unfold Valid; decide +kernel
theorem distinct6 : Trace triples6 seen6 seen7 := by unfold Trace; decide +kernel
noncomputable def triples7 : List Line := signedLines% "9,50,59,0;9,52,61,0;9,54,63,0;10,17,27,0;10,19,25,1;10,21,31,0;10,23,29,1;10,32,42,0;10,34,40,0;10,36,46,0;10,38,44,0;10,49,59,0;10,51,57,1;10,53,63,0;10,55,61,1;11,17,26,1"
theorem valid7 : Valid true triples7 := by unfold Valid; decide +kernel
theorem distinct7 : Trace triples7 seen7 seen8 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
