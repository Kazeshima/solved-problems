import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples28 : List Line := signedLines% "55,68,114,0;49,68,116,1;50,68,119,0;2,69,71,0;31,69,73,0;30,69,74,0;27,69,77,0;26,69,78,0;20,69,81,0;23,69,82,1;16,69,85,0;19,69,86,1;41,69,88,1;40,69,91,0;43,69,92,1;42,69,95,0"
theorem valid28 : Valid false triples28 := by unfold Valid; decide +kernel
theorem distinct28 : Trace triples28 seen28 seen29 := by unfold Trace; decide +kernel
noncomputable def triples29 : List Line := signedLines% "36,69,96,0;38,69,98,0;33,69,101,1;35,69,103,1;63,69,104,0;62,69,107,1;57,69,108,1;56,69,111,0;52,69,112,0;55,69,115,0;49,69,117,1;50,69,118,1;29,70,73,0;28,70,74,0;25,70,77,0;24,70,78,0"
theorem valid29 : Valid false triples29 := by unfold Valid; decide +kernel
theorem distinct29 : Trace triples29 seen29 seen30 := by unfold Trace; decide +kernel
noncomputable def triples30 : List Line := signedLines% "22,70,81,1;21,70,82,1;18,70,85,1;17,70,86,1;43,70,89,0;42,70,90,0;41,70,93,0;40,70,94,0;38,70,97,1;36,70,99,1;35,70,100,1;33,70,102,1;61,70,104,0;60,70,107,1;59,70,108,0;58,70,111,1"
theorem valid30 : Valid false triples30 := by unfold Valid; decide +kernel
theorem distinct30 : Trace triples30 seen30 seen31 := by unfold Trace; decide +kernel
noncomputable def triples31 : List Line := signedLines% "54,70,112,1;53,70,115,0;51,70,117,0;48,70,118,1;29,71,72,1;28,71,75,0;25,71,76,1;24,71,79,0;22,71,80,0;21,71,83,1;18,71,84,0;17,71,87,1;43,71,88,1;42,71,91,0;41,71,92,1;40,71,95,0"
theorem valid31 : Valid false triples31 := by unfold Valid; decide +kernel
theorem distinct31 : Trace triples31 seen31 seen32 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
