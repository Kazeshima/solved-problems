import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples60 : List Line := signedLines% "29,97,108,0;28,97,111,1;16,97,113,0;19,97,114,1;21,97,117,0;22,97,118,0;7,98,100,0;5,98,102,0;25,98,105,0;24,98,106,0;31,98,108,1;30,98,111,0;18,98,113,1;17,98,114,1;23,98,117,1;20,98,118,0"
theorem valid60 : Valid false triples60 := by unfold Valid; decide +kernel
theorem distinct60 : Trace triples60 seen60 seen61 := by unfold Trace; decide +kernel
noncomputable def triples61 : List Line := signedLines% "7,99,101,0;5,99,103,0;25,99,104,1;24,99,107,0;31,99,109,1;30,99,110,1;18,99,112,0;17,99,115,1;23,99,116,0;20,99,119,0;2,100,102,0;30,100,105,0;31,100,106,1;24,100,108,0;25,100,111,0;21,100,112,0"
theorem valid61 : Valid false triples61 := by unfold Valid; decide +kernel
theorem distinct61 : Trace triples61 seen61 seen62 := by unfold Trace; decide +kernel
noncomputable def triples62 : List Line := signedLines% "22,100,115,0;16,100,116,0;19,100,119,1;2,101,103,0;30,101,104,1;31,101,107,1;24,101,109,0;25,101,110,1;21,101,113,0;22,101,114,1;16,101,117,0;19,101,118,0;28,102,104,1;29,102,107,1;26,102,109,1;27,102,110,0"
theorem valid62 : Valid false triples62 := by unfold Valid; decide +kernel
theorem distinct62 : Trace triples62 seen62 seen63 := by unfold Trace; decide +kernel
noncomputable def triples63 : List Line := signedLines% "23,102,113,1;20,102,114,1;18,102,117,1;17,102,118,0;28,103,105,1;29,103,106,0;26,103,108,0;27,103,111,0;23,103,112,0;20,103,115,1;18,103,116,0;17,103,119,0;1,104,106,0;6,104,108,0;7,104,110,0;11,104,113,0"
theorem valid63 : Valid false triples63 := by unfold Valid; decide +kernel
theorem distinct63 : Trace triples63 seen63 seen64 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
