import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket12_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part1024_0 : List Witness := witnesses% "577028650067591176,567382631404552,36,24,4,2,1,66,69;577028650336026632,567391758210048,33,16,12,2,67,69;577028652483510280,567382631404552,39,27,4,2,1,64,65,66,67,68,69;577028658925961224,567382631404552,61,24,4,2,66,69;577028667515895816,567382631404552,62,24,4,1,66,69;577028650336026664,567382631404552,61,39,24,4,1,66,68,69,70;577028650336026696,567382631404552,62,39,24,4,2,66,67,69,70"
private theorem validpart1024_0 : part1024_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1024 : List Witness := part1024_0
theorem accepted1024 : records1024.all (validRecord false fullProfiles)=true := by
  exact validpart1024_0
noncomputable def records1056 : List Witness := []
theorem accepted1056 : records1056.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1088 : List Witness := []
theorem accepted1088 : records1088.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1120_0 : List Witness := witnesses% "580417409600508136,567382631404552,63,4,64,65,69,70"
private theorem validpart1120_0 : part1120_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1120 : List Witness := part1120_0
theorem accepted1120 : records1120.all (validRecord false fullProfiles)=true := by
  exact validpart1120_0
private noncomputable def part1152_0 : List Witness := witnesses% "649086244373954568,567382631404552,39,36,24,4,66,67,68,69,70"
private theorem validpart1152_0 : part1152_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1152 : List Witness := part1152_0
theorem accepted1152 : records1152.all (validRecord false fullProfiles)=true := by
  exact validpart1152_0
noncomputable def records1184 : List Witness := []
theorem accepted1184 : records1184.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1216 : List Witness := []
theorem accepted1216 : records1216.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1248 : List Witness := []
theorem accepted1248 : records1248.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1280 : List Witness := []
theorem accepted1280 : records1280.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1312 : List Witness := []
theorem accepted1312 : records1312.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1344 : List Witness := []
theorem accepted1344 : records1344.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1376 : List Witness := []
theorem accepted1376 : records1376.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1408 : List Witness := []
theorem accepted1408 : records1408.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1440 : List Witness := []
theorem accepted1440 : records1440.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1472_0 : List Witness := witnesses% "795741318004342952,567382631404552,46,18,10,4,2,1,64,66,67,68,69"
private theorem validpart1472_0 : part1472_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1472 : List Witness := part1472_0
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  exact validpart1472_0
private noncomputable def part1504_0 : List Witness := witnesses% "796304267957764264,567382631404552,63,53,17,4,64,66,67,69,70;796858421818163368,567382631404552,52,27,11,4,64,65,69,70;796867217906991272,567382631404552,45,27,9,4,65,67,69,70;796867217911185576,567391758210048,49,25,5,2,64,67;796868317422813352,567382631404552,27,10,8,4,65,68,69;796867217911189672,567382631404552,55,54,8,4,1,68,69,70;796867217911218344,567382631404552,60,39,10,8,4,67,69;796867217913282728,567382631404552,55,46,27,4,65,68,69"
private theorem validpart1504_0 : part1504_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1504 : List Witness := part1504_0
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  exact validpart1504_0
end Quadric.Five.Moves.RPacket12_2
