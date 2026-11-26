import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples12 : List Line := signedLines% "16,41,57,0;16,44,60,0;16,45,61,0;17,32,49,0;17,33,48,0;17,36,53,0;17,37,52,0;17,42,59,0;17,43,58,1;17,46,63,0;17,47,62,1;18,32,50,0;18,33,51,0;18,36,54,0;18,37,55,0;18,40,58,0"
theorem valid12 : Valid true triples12 := by unfold Valid; decide +kernel
theorem distinct12 : Trace triples12 seen12 seen13 := by unfold Trace; decide +kernel
noncomputable def triples13 : List Line := signedLines% "18,41,59,0;18,44,62,0;18,45,63,0;19,32,51,0;19,33,50,0;19,36,55,0;19,37,54,0;19,42,57,1;19,43,56,0;19,46,61,1;19,47,60,0;20,34,54,0;20,35,55,0;20,38,50,1;20,39,51,1;20,42,62,0"
theorem valid13 : Valid true triples13 := by unfold Valid; decide +kernel
theorem distinct13 : Trace triples13 seen13 seen14 := by unfold Trace; decide +kernel
noncomputable def triples14 : List Line := signedLines% "20,43,63,0;20,46,58,1;20,47,59,1;21,34,55,0;21,35,54,0;21,38,51,1;21,39,50,1;21,40,61,1;21,41,60,0;21,44,57,0;21,45,56,1;22,34,52,1;22,35,53,1;22,38,48,0;22,39,49,0;22,42,60,1"
theorem valid14 : Valid true triples14 := by unfold Valid; decide +kernel
theorem distinct14 : Trace triples14 seen14 seen15 := by unfold Trace; decide +kernel
noncomputable def triples15 : List Line := signedLines% "22,43,61,1;22,46,56,0;22,47,57,0;23,34,53,1;23,35,52,1;23,38,49,0;23,39,48,0;23,40,63,1;23,41,62,0;23,44,59,0;23,45,58,1;24,32,56,0;24,35,59,1;24,36,60,0;24,39,63,1;24,40,48,0"
theorem valid15 : Valid true triples15 := by unfold Valid; decide +kernel
theorem distinct15 : Trace triples15 seen15 seen16 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
