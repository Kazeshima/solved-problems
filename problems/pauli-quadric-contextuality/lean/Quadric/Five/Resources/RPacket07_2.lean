import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket07_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part1024_0 : List Witness := witnesses% "577028160704633856,4458448311296,40,23,18,65,67,69,70"
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
private noncomputable def part1120_0 : List Witness := witnesses% "579849511566986464,60401144832,61,49,20,11,2,66,68,69"
private theorem validpart1120_0 : part1120_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1120 : List Witness := part1120_0
theorem accepted1120 : records1120.all (validRecord false fullProfiles)=true := by
  exact validpart1120_0
noncomputable def records1152 : List Witness := []
theorem accepted1152 : records1152.all (validRecord false fullProfiles)=true := by
  rfl
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
private noncomputable def part1376_0 : List Witness := witnesses% "723955886369950944,36509335552,63,23,13,5,67,69;723955903549820128,4450394723328,40,27,18,12,65,67,69,70;723955903558208736,36509335552,46,23,13,7,5,1,65,66,67,68;723964682462973152,4449857851392,35,21,16,9,3,65,67,68,69;723964682471361760,4449857717248,63,36,23,5,64,65,66,67,69,70;723964695347875040,4432677983232,59,41,24,11,6,4,64,65,66,67,68;723964699642842336,4449857852416,40,27,18,12,65,67,69,70;723964699651230944,4449857721344,61,49,20,11,2,66,68,69;723964699911277792,4441267916800,46,36,23,13,3;723964700716584160,4449857852480,47,45,33,22,11,66,68,69;723964699642875104,4449857852480,45,27,22,8,65,67,69,70;723964699651263712,4449857848384,45,27,22,8,65,67,69,70;723964699643890912,4432677983232,40,27,18,12,65,67,69,70"
private theorem validpart1376_0 : part1376_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1376 : List Witness := part1376_0
theorem accepted1376 : records1376.all (validRecord false fullProfiles)=true := by
  exact validpart1376_0
noncomputable def records1408 : List Witness := []
theorem accepted1408 : records1408.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1440 : List Witness := []
theorem accepted1440 : records1440.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1472 : List Witness := []
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1504 : List Witness := []
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket07_2
