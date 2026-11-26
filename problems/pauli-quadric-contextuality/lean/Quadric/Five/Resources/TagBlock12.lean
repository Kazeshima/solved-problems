import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples48 : List Line := signedLines% "38,83,116,1;37,83,118,0;3,84,86,0;57,84,89,0;56,84,90,0;59,84,92,1;58,84,95,0;52,84,97,1;54,84,98,0;49,84,100,1;51,84,103,1;47,84,104,1;46,84,107,0;41,84,109,0;40,84,110,0;36,84,113,1"
theorem valid48 : Valid false triples48 := by unfold Valid; decide +kernel
theorem distinct48 : Trace triples48 seen48 seen49 := by unfold Trace; decide +kernel
noncomputable def triples49 : List Line := signedLines% "39,84,115,1;33,84,116,1;34,84,118,0;3,85,87,0;57,85,88,1;56,85,91,0;59,85,93,1;58,85,94,1;52,85,96,0;54,85,99,0;49,85,101,1;51,85,102,0;47,85,105,1;46,85,106,1;41,85,108,1;40,85,111,0"
theorem valid49 : Valid false triples49 := by unfold Valid; decide +kernel
theorem distinct49 : Trace triples49 seen49 seen50 := by unfold Trace; decide +kernel
noncomputable def triples50 : List Line := signedLines% "36,85,112,0;39,85,114,0;33,85,117,1;34,85,119,0;58,86,89,0;59,86,90,1;56,86,92,0;57,86,95,0;55,86,96,1;53,86,99,0;50,86,101,0;48,86,102,0;44,86,105,1;45,86,106,0;42,86,108,1;43,86,111,1"
theorem valid50 : Valid false triples50 := by unfold Valid; decide +kernel
theorem distinct50 : Trace triples50 seen50 seen51 := by unfold Trace; decide +kernel
noncomputable def triples51 : List Line := signedLines% "39,86,113,1;36,86,115,1;34,86,116,1;33,86,118,0;58,87,88,1;59,87,91,1;56,87,93,0;57,87,94,1;55,87,97,1;53,87,98,1;50,87,100,1;48,87,103,0;44,87,104,0;45,87,107,0;42,87,109,1;43,87,110,0"
theorem valid51 : Valid false triples51 := by unfold Valid; decide +kernel
theorem distinct51 : Trace triples51 seen51 seen52 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
