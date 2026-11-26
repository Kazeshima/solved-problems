import Quadric.Five.Resources.TagMasks

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable def triples44 : List Line := signedLines% "50,80,99,0;53,80,101,0;55,80,102,1;43,80,105,1;42,80,106,1;45,80,108,0;44,80,111,1;32,80,112,0;35,80,114,0;37,80,117,0;38,80,119,1;3,81,83,0;4,81,85,0;7,81,87,0;61,81,89,0;60,81,90,0"
theorem valid44 : Valid false triples44 := by unfold Valid; decide +kernel
theorem distinct44 : Trace triples44 seen44 seen45 := by unfold Trace; decide +kernel
noncomputable def triples45 : List Line := signedLines% "63,81,92,1;62,81,95,0;48,81,97,0;50,81,98,1;53,81,100,1;55,81,103,1;43,81,104,0;42,81,107,1;45,81,109,0;44,81,110,0;32,81,113,0;35,81,115,0;37,81,116,1;38,81,118,0;7,82,84,0;4,82,86,0"
theorem valid45 : Valid false triples45 := by unfold Valid; decide +kernel
theorem distinct45 : Trace triples45 seen45 seen46 := by unfold Trace; decide +kernel
noncomputable def triples46 : List Line := signedLines% "62,82,88,0;63,82,91,0;60,82,93,1;61,82,94,0;51,82,97,1;49,82,98,1;54,82,100,0;52,82,103,1;40,82,104,0;41,82,107,0;46,82,109,0;47,82,110,1;35,82,112,0;32,82,114,0;38,82,117,0;37,82,119,1"
theorem valid46 : Valid false triples46 := by unfold Valid; decide +kernel
theorem distinct46 : Trace triples46 seen46 seen47 := by unfold Trace; decide +kernel
noncomputable def triples47 : List Line := signedLines% "7,83,85,0;4,83,87,0;62,83,89,0;63,83,90,1;60,83,92,0;61,83,95,0;51,83,96,0;49,83,99,1;54,83,101,0;52,83,102,0;40,83,105,0;41,83,106,1;46,83,108,1;47,83,111,1;35,83,113,0;32,83,115,0"
theorem valid47 : Valid false triples47 := by unfold Valid; decide +kernel
theorem distinct47 : Trace triples47 seen47 seen48 := by unfold Trace; decide +kernel
end Quadric.Five.Tagged.Data
