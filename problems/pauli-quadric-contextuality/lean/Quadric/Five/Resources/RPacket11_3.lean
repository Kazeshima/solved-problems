import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket11_3
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
private noncomputable def part1632_0 : List Witness := witnesses% "868068829329924288,36509335552,42,39,26,8,7,64,65,66,67,68,69,70"
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
private noncomputable def part1760_0 : List Witness := witnesses% "940126423367844032,4449857717248,50,6,65,68,69;940126423367852224,4449857721344,20,6,1,65,67,69,70;940126425515335872,4449857717248,54,36,20,1,65,67,69,70;940126423367868608,36509335552,62,51,31,4,3,65,69,70;940128622391107776,4449857848384,55,24,23,12,7,67,68"
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
noncomputable def records1952 : List Witness := []
theorem accepted1952 : records1952.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1984 : List Witness := []
theorem accepted1984 : records1984.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part2016_0 : List Witness := witnesses% "1084525287591116928,4449857717248,50,9,6,4,64,68,70"
private theorem validpart2016_0 : part2016_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records2016 : List Witness := part2016_0
theorem accepted2016 : records2016.all (validRecord false fullProfiles)=true := by
  exact validpart2016_0
end Quadric.Five.Moves.RPacket11_3
