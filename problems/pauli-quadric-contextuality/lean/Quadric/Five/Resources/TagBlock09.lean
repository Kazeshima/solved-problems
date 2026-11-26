import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples36 : List Line := signedLines% "55,74,88,0;54,74,90,0;53,74,93,1;52,74,95,1;58,74,97,0;56,74,98,0;63,74,101,1;61,74,102,1;33,74,104,0;32,74,106,0;39,74,109,0;38,74,111,0;42,74,112,1;41,74,115,1;47,74,116,0;44,74,119,0"
theorem valid36 : Valid false triples36 := by unfold Valid; decide +kernel
theorem distinct36 : Trace triples36 seen36 seen37 := by unfold Trace; decide +kernel
noncomputable def triples37 : List Line := signedLines% "5,75,77,0;4,75,79,0;10,75,81,1;9,75,82,0;14,75,85,1;13,75,86,0;55,75,89,0;54,75,91,0;53,75,92,0;52,75,94,0;58,75,96,1;56,75,99,0;63,75,100,0;61,75,103,1;33,75,105,0;32,75,107,0"
theorem valid37 : Valid false triples37 := by unfold Valid; decide +kernel
theorem distinct37 : Trace triples37 seen37 seen38 := by unfold Trace; decide +kernel
noncomputable def triples38 : List Line := signedLines% "39,75,108,1;38,75,110,1;42,75,113,1;41,75,114,0;47,75,117,0;44,75,118,1;1,76,78,0;15,76,81,0;12,76,82,0;11,76,85,0;8,76,86,0;50,76,89,0;51,76,91,0;48,76,92,0;49,76,94,0;63,76,97,1"
theorem valid38 : Valid false triples38 := by unfold Valid; decide +kernel
theorem distinct38 : Trace triples38 seen38 seen39 := by unfold Trace; decide +kernel
noncomputable def triples39 : List Line := signedLines% "61,76,98,1;58,76,101,0;56,76,102,0;36,76,105,1;37,76,107,1;34,76,108,1;35,76,110,1;47,76,112,0;44,76,115,1;42,76,116,1;41,76,119,0;1,77,79,0;15,77,80,1;12,77,83,0;11,77,84,1;8,77,87,0"
theorem valid39 : Valid false triples39 := by unfold Valid; decide +kernel
theorem distinct39 : Trace triples39 seen39 seen40 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
