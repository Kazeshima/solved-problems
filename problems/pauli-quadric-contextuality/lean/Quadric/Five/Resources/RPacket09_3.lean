import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket09_3
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records1536 : List Witness := []
theorem accepted1536 : records1536.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1568 : List Witness := []
theorem accepted1568 : records1568.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1600 : List Witness := []
theorem accepted1600 : records1600.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1632_0 : List Witness := witnesses% "868079823301148896,4449857852424,35,28,16,12,7,64,65,69;868079823301157088,4450394723336,52,51,24,12,3,65,66,67,68,69"
private theorem validpart1632_0 : part1632_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1632 : List Witness := part1632_0
theorem accepted1632 : records1632.all (validRecord false fullProfiles)=true := by
  exact validpart1632_0
noncomputable def records1664 : List Witness := []
theorem accepted1664 : records1664.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1696 : List Witness := []
theorem accepted1696 : records1696.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1728 : List Witness := []
theorem accepted1728 : records1728.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1760_0 : List Witness := witnesses% "940126423300743360,60401143808,56,24,12,5,2,64,65,67,68,69"
private theorem validpart1760_0 : part1760_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1760 : List Witness := part1760_0
theorem accepted1760 : records1760.all (validRecord false fullProfiles)=true := by
  exact validpart1760_0
noncomputable def records1792 : List Witness := []
theorem accepted1792 : records1792.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1824 : List Witness := []
theorem accepted1824 : records1824.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1856 : List Witness := []
theorem accepted1856 : records1856.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1888 : List Witness := []
theorem accepted1888 : records1888.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1920 : List Witness := []
theorem accepted1920 : records1920.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1952_0 : List Witness := witnesses% "1082839739419893760,4449857852424,44,43,16,12,8,64,65,66,69;1082839740493635584,4450394723336,35,28,23,11,67,68,69;1082841938443141120,4449857852424,50,39,25,20,9,7,64,69,70;1082841938443149312,4458447787016,35,28,23,11,67,68,69;1082841939516891136,4449857852424,35,28,23,11,67,68,69"
private theorem validpart1952_0 : part1952_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1952 : List Witness := part1952_0
theorem accepted1952 : records1952.all (validRecord false fullProfiles)=true := by
  exact validpart1952_0
noncomputable def records1984 : List Witness := []
theorem accepted1984 : records1984.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records2016 : List Witness := []
theorem accepted2016 : records2016.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket09_3
