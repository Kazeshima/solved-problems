import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket13_3
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records1536 : List Witness := []
theorem accepted1536 : records1536.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1568_0 : List Witness := witnesses% "865823077823472712,4458447787200,29,13,9,2,1,65,67,68,69;865824226729313480,4458447787200,49,42,8,5,4,64,66,69,70"
private theorem validpart1568_0 : part1568_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1568 : List Witness := part1568_0
theorem accepted1568 : records1568.all (validRecord false fullProfiles)=true := by
  exact validpart1568_0
noncomputable def records1600 : List Witness := []
theorem accepted1600 : records1600.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1632 : List Witness := []
theorem accepted1632 : records1632.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1664 : List Witness := []
theorem accepted1664 : records1664.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1696 : List Witness := []
theorem accepted1696 : records1696.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1728 : List Witness := []
theorem accepted1728 : records1728.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1760 : List Witness := []
theorem accepted1760 : records1760.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1792 : List Witness := []
theorem accepted1792 : records1792.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1824 : List Witness := []
theorem accepted1824 : records1824.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1856 : List Witness := []
theorem accepted1856 : records1856.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1888_0 : List Witness := witnesses% "1012195625550234856,4458447787200,61,21,17,5,2,64,69"
private theorem validpart1888_0 : part1888_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1888 : List Witness := part1888_0
theorem accepted1888 : records1888.all (validRecord false fullProfiles)=true := by
  exact validpart1888_0
noncomputable def records1920 : List Witness := []
theorem accepted1920 : records1920.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1952 : List Witness := []
theorem accepted1952 : records1952.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1984 : List Witness := []
theorem accepted1984 : records1984.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part2016_0 : List Witness := witnesses% "1084526949667202248,4458447787200,57,42,6,5,4,65,67,70"
private theorem validpart2016_0 : part2016_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records2016 : List Witness := part2016_0
theorem accepted2016 : records2016.all (validRecord false fullProfiles)=true := by
  exact validpart2016_0
end Quadric.Five.Moves.RPacket13_3
