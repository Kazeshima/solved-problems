import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples0 : List Line := signedLines% "1,2,3,0;1,4,5,0;1,6,7,0;1,16,17,0;1,18,19,0;1,20,21,0;1,22,23,0;1,32,33,0;1,34,35,0;1,36,37,0;1,38,39,0;1,48,49,0;1,50,51,0;1,52,53,0;1,54,55,0;2,4,6,0"
theorem valid0 : Valid true triples0 := by unfold Valid; decide +kernel
theorem distinct0 : Trace triples0 seen0 seen1 := by unfold Trace; decide +kernel
noncomputable def triples1 : List Line := signedLines% "2,5,7,0;2,8,10,0;2,9,11,0;2,12,14,0;2,13,15,0;2,32,34,0;2,33,35,0;2,36,38,0;2,37,39,0;2,40,42,0;2,41,43,0;2,44,46,0;2,45,47,0;3,4,7,0;3,5,6,0;3,24,27,1"
theorem valid1 : Valid true triples1 := by unfold Valid; decide +kernel
theorem distinct1 : Trace triples1 seen1 seen2 := by unfold Trace; decide +kernel
noncomputable def triples2 : List Line := signedLines% "3,25,26,0;3,28,31,1;3,29,30,0;3,32,35,0;3,33,34,0;3,36,39,0;3,37,38,0;3,56,59,1;3,57,58,0;3,60,63,1;3,61,62,0;4,8,12,0;4,9,13,0;4,10,14,0;4,11,15,0;4,16,20,0"
theorem valid2 : Valid true triples2 := by unfold Valid; decide +kernel
theorem distinct2 : Trace triples2 seen2 seen3 := by unfold Trace; decide +kernel
noncomputable def triples3 : List Line := signedLines% "4,17,21,0;4,18,22,0;4,19,23,0;4,24,28,0;4,25,29,0;4,26,30,0;4,27,31,0;5,16,21,0;5,17,20,0;5,18,23,0;5,19,22,0;5,40,45,1;5,41,44,0;5,42,47,1;5,43,46,0;5,56,61,1"
theorem valid3 : Valid true triples3 := by unfold Valid; decide +kernel
theorem distinct3 : Trace triples3 seen3 seen4 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
