import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket05_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part1024_0 : List Witness := witnesses% "577028160704631816,4458456175616,60,58,24,20,64,66,68,69"
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
private noncomputable def part1120_0 : List Witness := witnesses% "579849511566984424,567382631404552,63,27,64,65,67,68"
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
private noncomputable def part1312_0 : List Witness := witnesses% "721712899829154984,4450394723336,51,38,10,7,6,2,65,66,69;721712899829155048,4449857852424,44,38,21,7,6,2,67,69"
private theorem validpart1312_0 : part1312_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1312 : List Witness := part1312_0
theorem accepted1312 : records1312.all (validRecord false fullProfiles)=true := by
  exact validpart1312_0
private noncomputable def part1344_0 : List Witness := witnesses% "722838799735997608,4450394723336,50,39,14,3,65,66,68;722838799735997672,4449857852424,41,39,21,3,64,66,67"
private theorem validpart1344_0 : part1344_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1344 : List Witness := part1344_0
theorem accepted1344 : records1344.all (validRecord false fullProfiles)=true := by
  exact validpart1344_0
private noncomputable def part1376_0 : List Witness := witnesses% "723955903549818024,283540423974912,41,39,37,22,18,1,64,66,68,70;723955886369948904,4449857848384,32,22,19,14,10,64,65,67,68,69,70;723955899254850792,567356870022144,54,24,19,14,8,1,65,69,70;723955903549818088,4458447782976,41,21,15,6,68;723964699642823848,4450394723336,63,27,64,65,67,68;723964699642823912,4449857852424,63,27,64,65,67,68;723964665283101864,283540423974912,46,30,10,6,4,1,64,65,66,68,69,70;723964682462971048,283540423974912,43,25,20,7,4,64,65,68,70;723964691052905640,4450394723336,49,44,21,6,5,67,69;723964695347872936,4450394723336,48,41,21,6,4,1,64,66,67,68,69;723964699642840232,567391229726720,58,24,23,3,65,67,69,70;723964699651228840,60401143808,42,26,21,6,2,68;723964700179711144,4450394723336,58,30,22,13,5,64,67,69;723964700716582056,283540423974912,58,45,28,14,6,68,70;723964699642840264,567382631404552,41,39,21,3,64,66,67;723964648103232744,567356870022144,60,19,14,10,3,65,66,68,69;723964656693167336,567356870022144,58,24,23,3,65,67,69,70;723964665283101928,4458447782976,33,23,18,12,65,67,68,69;723964665291490536,4449857848384,63,54,26,4,65,66,68,69;723964678168003816,567356870022144,34,22,10,2,1,64,65,68,69,70;723964682462971112,4458447782976,32,22,19,12,65,67,68,69;723964682471359720,4449857848384,32,22,19,12,65,67,68,69;723964683536712936,283540423974912,54,34,23,19,9,1,64,65,66,67,68,69;723964686757938408,567356870022144,35,17,7,5,2,67,69;723964691052905704,567374049891328,35,17,7,5,2,67,69;723964691589776616,4450394723336,52,30,22,3,65,66,68,69,70;723964695347873000,567374049891328,34,30,29,12,64,65,67,69;723964699642840296,567382631404544,45,30,9,5,64,65,67,68;723964699651228904,4449857721344,54,29,26,14,4,65,67,69,70;723964700179711208,4450394723328,52,30,22,3,65,66,68,69,70;723964700188099816,36509335552,53,36,12,7,4,68,70;723964700716582120,4458447782976,50,46,30,21,12,1,64,65,70;723964699642844328,283540423974912,52,35,14,6,5,68,70;723964699642844392,4432677983232,53,36,25,23,7,65,67,68,69;723964699642873064,4441267916800,58,52,23,6,4,1,64,67,68,70;723964699643888808,4450394723336,45,35,16,11,3,1,64,68;723964699643888872,4450394723328,53,26,18,4,3,66,68,69,70;723964700180759784,36509335552,45,23,5,2,1,64,68,69;724246174619550888,60401143808,56,48,24,13,2,65,66,68;724246174619550952,60401144832,49,26,21,6,3,67,68;724527649596261544,60401143808,48,29,8,4,2;724527649596261608,60401144832,48,30,21,7,2,67,68"
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
private noncomputable def part1472_0 : List Witness := witnesses% "795177826346206376,4449857852480,63,31,15,11,1,67,70;795177826350400680,567356870022144,20,17,12,10,8,64,67,69,70"
private theorem validpart1472_0 : part1472_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1472 : List Witness := part1472_0
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  exact validpart1472_0
private noncomputable def part1504_0 : List Witness := witnesses% "796022293680768168,283540423974912,46,13,11,6,3,66,68,70;796022293680768232,4432677983232,40,25,23,4,3,1,64,69;796303726253049000,4449857848384,63,31,15,11,1,67,70;796303718202082472,4449857848384,52,44,23,11,3,1,64,65,66,67;796304811808171176,283540423974912,58,52,35,17,64,66,67,68;796304811808171240,4432677983232,43,25,20,4,3,1,64,65,68,70;796866668155503784,4449857852480,52,44,23,11,3,1,64,65,66,67;796866668157600936,567356870022144,57,44,41,15,2,1,65,66,69"
private theorem validpart1504_0 : part1504_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1504 : List Witness := part1504_0
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  exact validpart1504_0
end Quadric.Five.Moves.RPacket05_2
