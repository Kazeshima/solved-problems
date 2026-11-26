import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples64 : List Line := signedLines% "8,104,114,0;14,104,116,0;13,104,119,1;1,105,107,0;6,105,109,0;7,105,111,0;11,105,112,1;8,105,115,0;14,105,117,0;13,105,118,0;7,106,108,0;6,106,110,0;10,106,112,1;9,106,115,1;15,106,117,1;12,106,118,0"
theorem valid64 : Valid false triples64 := by unfold Valid; decide +kernel
theorem distinct64 : Trace triples64 seen64 seen65 := by unfold Trace; decide +kernel
noncomputable def triples65 : List Line := signedLines% "7,107,109,0;6,107,111,0;10,107,113,1;9,107,114,0;15,107,116,0;12,107,119,0;1,108,110,0;13,108,113,0;14,108,114,0;8,108,116,0;11,108,119,1;1,109,111,0;13,109,112,1;14,109,115,0;8,109,117,0;11,109,118,0"
theorem valid65 : Valid false triples65 := by unfold Valid; decide +kernel
theorem distinct65 : Trace triples65 seen65 seen66 := by unfold Trace; decide +kernel
noncomputable def triples66 : List Line := signedLines% "12,110,112,1;15,110,115,1;9,110,117,1;10,110,118,0;12,111,113,1;15,111,114,0;9,111,116,0;10,111,119,0;3,112,114,0;5,112,116,0;6,112,118,1;3,113,115,0;5,113,117,0;6,113,119,1;6,114,116,0;5,114,118,1"
theorem valid66 : Valid false triples66 := by unfold Valid; decide +kernel
theorem distinct66 : Trace triples66 seen66 seen67 := by unfold Trace; decide +kernel
noncomputable def triples67 : List Line := signedLines% "6,115,117,0;5,115,119,1;3,116,118,1;3,117,119,1"
theorem valid67 : Valid false triples67 := by unfold Valid; decide +kernel
theorem distinct67 : Trace triples67 seen67 seen68 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
