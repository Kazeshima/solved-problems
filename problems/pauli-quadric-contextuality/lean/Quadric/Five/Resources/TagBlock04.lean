import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples16 : List Line := signedLines% "24,43,51,0;24,44,52,0;24,47,55,0;25,32,57,0;25,35,58,0;25,36,61,0;25,39,62,0;25,41,48,0;25,42,51,1;25,45,52,0;25,46,55,1;26,32,58,0;26,35,57,0;26,36,62,0;26,39,61,0;26,40,50,0"
theorem valid16 : Valid true triples16 := by unfold Valid; decide +kernel
theorem distinct16 : Trace triples16 seen16 seen17 := by unfold Trace; decide +kernel
noncomputable def triples17 : List Line := signedLines% "26,43,49,1;26,44,54,0;26,47,53,1;27,32,59,0;27,35,56,1;27,36,63,0;27,39,60,1;27,41,50,0;27,42,49,0;27,45,54,0;27,46,53,0;28,33,61,0;28,34,62,0;28,37,57,1;28,38,58,1;28,41,53,1"
theorem valid17 : Valid true triples17 := by unfold Valid; decide +kernel
theorem distinct17 : Trace triples17 seen17 seen18 := by unfold Trace; decide +kernel
noncomputable def triples18 : List Line := signedLines% "28,42,54,0;28,45,49,0;28,46,50,1;29,33,60,1;29,34,63,0;29,37,56,0;29,38,59,1;29,40,53,0;29,43,54,0;29,44,49,1;29,47,50,1;30,33,63,0;30,34,60,1;30,37,59,1;30,38,56,0;30,41,55,1"
theorem valid18 : Valid true triples18 := by unfold Valid; decide +kernel
theorem distinct18 : Trace triples18 seen18 seen19 := by unfold Trace; decide +kernel
noncomputable def triples19 : List Line := signedLines% "30,42,52,1;30,45,51,0;30,46,48,0;31,33,62,1;31,34,61,1;31,37,58,0;31,38,57,0;31,40,55,0;31,43,52,1;31,44,51,1;31,47,48,0"
theorem valid19 : Valid true triples19 := by unfold Valid; decide +kernel
theorem distinct19 : Trace triples19 seen19 seen20 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
