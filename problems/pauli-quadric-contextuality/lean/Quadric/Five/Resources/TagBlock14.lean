import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples56 : List Line := signedLines% "13,92,99,0;10,92,100,0;8,92,102,0;20,92,104,1;21,92,106,1;18,92,109,1;19,92,111,1;31,92,112,0;28,92,114,1;26,92,117,1;25,92,119,0;1,93,95,0;15,93,96,1;13,93,98,1;10,93,101,0;8,93,103,0"
theorem valid56 : Valid false triples56 := by unfold Valid; decide +kernel
theorem distinct56 : Trace triples56 seen56 seen57 := by unfold Trace; decide +kernel
noncomputable def triples57 : List Line := signedLines% "20,93,105,1;21,93,107,1;18,93,108,0;19,93,110,0;31,93,113,0;28,93,115,1;26,93,116,0;25,93,118,1;14,94,96,1;12,94,98,1;11,94,101,1;9,94,103,1;21,94,104,1;20,94,106,1;19,94,109,1;18,94,111,1"
theorem valid57 : Valid false triples57 := by unfold Valid; decide +kernel
theorem distinct57 : Trace triples57 seen57 seen58 := by unfold Trace; decide +kernel
noncomputable def triples58 : List Line := signedLines% "30,94,113,0;29,94,115,0;27,94,116,1;24,94,118,1;14,95,97,1;12,95,99,1;11,95,100,0;9,95,102,0;21,95,105,1;20,95,107,1;19,95,108,0;18,95,110,0;30,95,112,1;29,95,114,1;27,95,117,1;24,95,119,1"
theorem valid58 : Valid false triples58 := by unfold Valid; decide +kernel
theorem distinct58 : Trace triples58 seen58 seen59 := by unfold Trace; decide +kernel
noncomputable def triples59 : List Line := signedLines% "2,96,98,0;5,96,100,0;7,96,102,0;27,96,104,0;26,96,107,1;29,96,109,1;28,96,110,1;16,96,112,0;19,96,115,0;21,96,116,0;22,96,119,1;2,97,99,0;5,97,101,0;7,97,103,0;27,97,105,0;26,97,106,0"
theorem valid59 : Valid false triples59 := by unfold Valid; decide +kernel
theorem distinct59 : Trace triples59 seen59 seen60 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
