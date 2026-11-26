import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket14_1
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part512_0 : List Witness := witnesses% "288798334307685384,4449857848384,50,18,11,9,2,1,64,67,70;288798334308733960,4449857721344,49,22,19,9,5,65,68,69;288799433820361736,4449857717248,53,25,23,7,65,67,68,69;288798334308734024,60401143808,58,32,12,5,2,65,66,68,70;288807130401756168,36509335552,43,18,6,2,1,67,68"
private theorem validpart512_0 : part512_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records512 : List Witness := part512_0
theorem accepted512 : records512.all (validRecord false fullProfiles)=true := by
  exact validpart512_0
noncomputable def records544 : List Witness := []
theorem accepted544 : records544.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records576 : List Witness := []
theorem accepted576 : records576.all (validRecord false fullProfiles)=true := by
  rfl
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
noncomputable def records768 : List Witness := []
theorem accepted768 : records768.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records800 : List Witness := []
theorem accepted800 : records800.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records832 : List Witness := []
theorem accepted832 : records832.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part864_0 : List Witness := witnesses% "435734873246942440,4458447787200,56,45,40,3,1,65,66,67,68"
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
end Quadric.Five.Moves.RPacket14_1
