import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket07_1
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part512_0 : List Witness := witnesses% "288797784551873536,4449857852424,52,30,8,5,3,1,64,66,67,69;288797784552922112,4458447787072,54,29,23,5,3,66,68,69,70;288797785626663936,4449857852480,35,26,12,5,2,64,65;288797788847889408,4449857852424,49,32,23,19,8,64,65,67,70;288798884064549888,4458447787200,49,33,29,9,1,69;288797784552922176,4458447782976,41,37,21,13,11,2,64,65;288797784552930304,4432677983232,57,30,11,5;288797784552954880,4449857852480,60,27,22,14,8,1,66,67,68,69,70;288797784552954944,4449857848384,60,27,22,14,8,1,66,67,68,69,70;288806580645944320,567374049891328,33,27,12,5,65,68;288806580645944384,567356870022144,33,27,12,5,65,68"
private theorem validpart512_0 : part512_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records512 : List Witness := part512_0
theorem accepted512 : records512.all (validRecord false fullProfiles)=true := by
  exact validpart512_0
noncomputable def records544 : List Witness := []
theorem accepted544 : records544.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part576_0 : List Witness := witnesses% "291049584366607360,4449857852480,60,42,34,19,3,1,67,69;291049584366607424,4449857848384,60,42,34,19,3,1,67,69;291058380459629568,567356870022144,55,46,14,7,2,64,65,69"
private theorem validpart576_0 : part576_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records576 : List Witness := part576_0
theorem accepted576 : records576.all (validRecord false fullProfiles)=true := by
  exact validpart576_0
noncomputable def records608 : List Witness := []
theorem accepted608 : records608.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records640 : List Witness := []
theorem accepted640 : records640.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records672 : List Witness := []
theorem accepted672 : records672.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records704 : List Witness := []
theorem accepted704 : records704.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records736 : List Witness := []
theorem accepted736 : records736.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part768_0 : List Witness := witnesses% "432912972628777984,4432677983232,63,58,16,13,11,3,64,67,68,69,70"
private theorem validpart768_0 : part768_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records768 : List Witness := part768_0
theorem accepted768 : records768.all (validRecord false fullProfiles)=true := by
  exact validpart768_0
noncomputable def records800 : List Witness := []
theorem accepted800 : records800.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records832 : List Witness := []
theorem accepted832 : records832.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part864_0 : List Witness := witnesses% "435734323491130592,2251136434344,63,58,25,13,64,68,69,70"
private theorem validpart864_0 : part864_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records864 : List Witness := part864_0
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  exact validpart864_0
noncomputable def records896 : List Witness := []
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records928 : List Witness := []
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records960 : List Witness := []
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records992 : List Witness := []
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket07_1
