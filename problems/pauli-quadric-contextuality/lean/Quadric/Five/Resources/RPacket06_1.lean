import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket06_1
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
private noncomputable def part608_0 : List Witness := witnesses% "292176588076931136,60401144832,52,45,7,4,64,66,67,68,70;292176588077979712,60401143808,52,45,7,4,64,66,67,68,70"
private theorem validpart608_0 : part608_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records608 : List Witness := part608_0
theorem accepted608 : records608.all (validRecord false fullProfiles)=true := by
  exact validpart608_0
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
noncomputable def records864 : List Witness := []
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part896_0 : List Witness := witnesses% "504698985415583744,60401144832,61,31,22,12,10,64,65,67,68,69;504698985684019200,60401143808,61,19,10,7,4,69;504701184438839296,60401275904,61,19,10,7,4,69;504701184707274752,60401144832,61,19,10,7,4,69"
private theorem validpart896_0 : part896_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records896 : List Witness := part896_0
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  exact validpart896_0
noncomputable def records928 : List Witness := []
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records960 : List Witness := []
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records992 : List Witness := []
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket06_1
