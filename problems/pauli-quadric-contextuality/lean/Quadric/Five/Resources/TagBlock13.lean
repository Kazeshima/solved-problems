import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples52 : List Line := signedLines% "39,87,112,0;36,87,114,0;34,87,117,1;33,87,119,0;1,88,90,0;2,88,92,0;3,88,94,0;13,88,97,0;15,88,99,0;8,88,100,0;10,88,102,0;22,88,105,0;23,88,107,0;16,88,108,0;17,88,110,0;29,88,113,0"
theorem valid52 : Valid false triples52 := by unfold Valid; decide +kernel
theorem distinct52 : Trace triples52 seen52 seen53 := by unfold Trace; decide +kernel
noncomputable def triples53 : List Line := signedLines% "30,88,115,0;24,88,116,0;27,88,118,0;1,89,91,0;2,89,93,0;3,89,95,0;13,89,96,1;15,89,98,1;8,89,101,0;10,89,103,0;22,89,104,1;23,89,106,1;16,89,109,0;17,89,111,0;29,89,112,1;30,89,114,1"
theorem valid53 : Valid false triples53 := by unfold Valid; decide +kernel
theorem distinct53 : Trace triples53 seen53 seen54 := by unfold Trace; decide +kernel
noncomputable def triples54 : List Line := signedLines% "24,89,117,0;27,89,119,0;3,90,92,0;2,90,94,0;12,90,96,1;14,90,98,1;9,90,101,1;11,90,103,1;23,90,105,0;22,90,107,0;17,90,108,0;16,90,110,0;28,90,112,1;31,90,114,0;25,90,117,1;26,90,119,0"
theorem valid54 : Valid false triples54 := by unfold Valid; decide +kernel
theorem distinct54 : Trace triples54 seen54 seen55 := by unfold Trace; decide +kernel
noncomputable def triples55 : List Line := signedLines% "3,91,93,0;2,91,95,0;12,91,97,1;14,91,99,1;9,91,100,0;11,91,102,0;23,91,104,1;22,91,106,1;17,91,109,0;16,91,111,0;28,91,113,1;31,91,115,0;25,91,116,0;26,91,118,1;1,92,94,0;15,92,97,0"
theorem valid55 : Valid false triples55 := by unfold Valid; decide +kernel
theorem distinct55 : Trace triples55 seen55 seen56 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
