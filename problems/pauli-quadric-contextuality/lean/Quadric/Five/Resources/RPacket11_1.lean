import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket11_1
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records512 : List Witness := []
theorem accepted512 : records512.all (validRecord false fullProfiles)=true := by
  rfl
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
private noncomputable def part736_0 : List Witness := witnesses% "363665671064428736,4449857848384,39,26,15,6,65,66,67,68,69"
private theorem validpart736_0 : part736_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records736 : List Witness := part736_0
theorem accepted736 : records736.all (validRecord false fullProfiles)=true := by
  exact validpart736_0
noncomputable def records768 : List Witness := []
theorem accepted768 : records768.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records800 : List Witness := []
theorem accepted800 : records800.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records832 : List Witness := []
theorem accepted832 : records832.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records864 : List Witness := []
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records896 : List Witness := []
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records928 : List Witness := []
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records960 : List Witness := []
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part992_0 : List Witness := witnesses% "508062336264437888,4449857717248,36,20,9,1,64,66,67,69;508064535287693312,36509335552,62,51,26,5,3,64,65,68;508064533140209792,4449857848384,40,32,17,11,5,64,66,68,69,70;508064535287693440,4449857721344,36,20,9,1,64,66,67,69;508064535287701632,4449857848384,53,47,23,19,1,64,65,66,67,70;508627485241114752,36509335552,44,33,8,5,3"
private theorem validpart992_0 : part992_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records992 : List Witness := part992_0
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  exact validpart992_0
end Quadric.Five.Moves.RPacket11_1
