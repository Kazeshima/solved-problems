import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket10_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part1024_0 : List Witness := witnesses% "577320635118127136,4458456175616,63,53,16,7,5,1,64,65,66,69"
private theorem validpart1024_0 : part1024_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1024 : List Witness := part1024_0
theorem accepted1024 : records1024.all (validRecord false fullProfiles)=true := by
  exact validpart1024_0
private noncomputable def part1056_0 : List Witness := witnesses% "577597647352269024,4458456175616,30,21,15,6,2,1,67,70"
private theorem validpart1056_0 : part1056_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1056 : List Witness := part1056_0
theorem accepted1056 : records1056.all (validRecord false fullProfiles)=true := by
  exact validpart1056_0
private noncomputable def part1088_0 : List Witness := witnesses% "578723547259111648,4458456175616,39,38,26,15,13,64,67,68,69"
private theorem validpart1088_0 : part1088_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1088 : List Witness := part1088_0
theorem accepted1088 : records1088.all (validRecord false fullProfiles)=true := by
  exact validpart1088_0
private noncomputable def part1120_0 : List Witness := witnesses% "579840651072932064,4458456175616,16,9,6,4,64,68,70;579847248142698720,4458456175616,43,41,22,64,65,67,68;579849447165921504,4458456175616,60,24,9,6,4,1,64,65,66,69;579849447165954144,4458456175616,60,44,9,6,4,64,66,67,69,70;579849447165954208,4458456175616,58,43,28,19,1,65,68,69,70;579849447165954240,4458456175616,55,37,36,8,6,4,64,65,66,67,68,70;579849447157565664,4458456175616,36,9,6,4,1,64,66,67,68;579849447165954272,567408401208832,54,31,14,3,64,65,67,68,69;579849447434389728,4458456175616,45,35,33,3,64,66,68;579849447702825184,4458456175616,51,33,16,8,1,64,66;579849448239696096,4458456175616,41,32,26,17,1,66,67;579849449313437920,4458456175616,44,36,24,9,6,4,64,66,67,69,70;579849451460921568,4458456175616,51,32,30,17,11,1,67,68,70;579849455755888864,4458456175616,44,43,41,29,1,64,69;579849464345823456,4458456175616,53,26,7,5,3,66,68;579849481525692640,4458456175616,59,42,37,19,64,65,67,68,69;579850546677582048,4458456175616,39,27,9,6,4,1,64,65,66,67,68,70;579849447165958368,4458456175616,50,41,28,20,5,1,66,67;579849447165962464,4458456175616,49,43,24,23,1,65,68,70;579849447165970656,4458456175616,49,43,39,24,66,69;579849447167002848,4458456175616,38,37,17,14,12,64,68,69;579849447168051424,4458456175616,34,32,30,21,1,67,68,69;579849447170148576,4458456175616,48,41,23,12,64,65,66,67,68,70;579853845212465376,4458456175616,48,41,28,27,11,64,66,67,68,70;580130922142664928,4458456175616,63,10,7,5,2,64,65,67,69,70;580406964245813312,4458456175616,38,11,6,4,1,64,67,68,69;580412397119375584,4458456175616,38,15,13,1,64,66,67,68,69,70"
private theorem validpart1120_0 : part1120_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1120 : List Witness := part1120_0
theorem accepted1120 : records1120.all (validRecord false fullProfiles)=true := by
  exact validpart1120_0
private noncomputable def part1152_0 : List Witness := witnesses% "648532657996081152,4458456175616,52,18,10,6,4,64,65,66,68,70"
private theorem validpart1152_0 : part1152_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1152 : List Witness := part1152_0
theorem accepted1152 : records1152.all (validRecord false fullProfiles)=true := by
  exact validpart1152_0
noncomputable def records1184 : List Witness := []
theorem accepted1184 : records1184.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1216_0 : List Witness := witnesses% "651614581047171072,4458456175616,46,43,41,28,20,1,64,67,68,70"
private theorem validpart1216_0 : part1216_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1216 : List Witness := part1216_0
theorem accepted1216 : records1216.all (validRecord false fullProfiles)=true := by
  exact validpart1216_0
private noncomputable def part1248_0 : List Witness := witnesses% "651907041203882208,4458456175616,56,51,13,4,2,1,64,65,70"
private theorem validpart1248_0 : part1248_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1248 : List Witness := part1248_0
theorem accepted1248 : records1248.all (validRecord false fullProfiles)=true := by
  exact validpart1248_0
private noncomputable def part1280_0 : List Witness := witnesses% "720872873240561696,4458456175616,38,17,16,14,12,65,68,69,70;721154348217272352,4458456175616,58,50,14,4,2,1,64,65,66,69,70;721427027100960800,4458456175616,59,35,30,26,22,64,66,68;721431425147471904,4458456175616,54,27,24,15,13,66,67,68;721433624170727456,4458456175616,53,30,22,12,6,65,67,68,69;721435823191885856,4458456175616,43,41,20,8,1,66,67;721435823192934432,4458456175616,44,19,8,7,5,65,66,67,68,69;721435823193982976,4458456175616,54,19,8,6,4,65,66,67,68,69;721435788834244640,4458456175616,63,36,7,5,64,65,66,67,69;721435806014113824,4458456175616,50,46,41,25,1,64,66;721435814604048416,4458456175616,63,45,25,7,5,64,66,67,69,70;721435818899015712,4458456175616,52,44,7,5,3,67,69;721435822925547552,4458456175616,62,61,39,6,4,64,65,66,67,70;721435823185594400,4458456175616,36,18,8,6,4,65,69,70;721435823193983008,567408401208832,37,31,14,3,64,65,70;721435823730853920,4458456175616,46,25,9,6,4,1,64,70;721435824267724832,4458456175616,35,33,29,23,9,1,64,65,66,67,69;721435825341466656,4458456175616,40,32,27,17,3,64,65,66,68,69,70;721436922705610784,4458456175616,63,17,7,5,1,64,65,67,69,70;721435823193983072,4458456175616,59,42,30,13,64,68,70;721435823193983136,4458456175616,53,37,26,7,5,68,70;721435823193987104,4458456175616,52,27,11,7,5,64,65,67,68;721435823193991200,4458456175616,63,46,15,13,64,65,67,69,70;721435823193999392,4458456175616,61,9,7,5,2,64,67,68,70;721435823194015776,4458456175616,60,18,14,12,2,65,66,68,70;721435823198177312,4458456175616,40,34,23,18,13,1,64,65,66,67"
private theorem validpart1280_0 : part1280_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1280 : List Witness := part1280_0
theorem accepted1280 : records1280.all (validRecord false fullProfiles)=true := by
  exact validpart1280_0
private noncomputable def part1312_0 : List Witness := witnesses% "722561723100825632,4458456175616,46,26,11,7,5,1,64,67,68,70"
private theorem validpart1312_0 : part1312_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1312 : List Witness := part1312_0
theorem accepted1312 : records1312.all (validRecord false fullProfiles)=true := by
  exact validpart1312_0
private noncomputable def part1344_0 : List Witness := witnesses% "723687623007668256,4458456175616,27,17,9,7,5,1,65,67,68"
private theorem validpart1344_0 : part1344_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1344 : List Witness := part1344_0
theorem accepted1344 : records1344.all (validRecord false fullProfiles)=true := by
  exact validpart1344_0
private noncomputable def part1376_0 : List Witness := witnesses% "723964635241810144,4458456175616,57,44,35,22,14,8,64,66,67,68,70"
private theorem validpart1376_0 : part1376_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1376 : List Witness := part1376_0
theorem accepted1376 : records1376.all (validRecord false fullProfiles)=true := by
  exact validpart1376_0
private noncomputable def part1408_0 : List Witness := witnesses% "793493417231910944,4458456175616,16,14,12,10,1,64,67,69"
private theorem validpart1408_0 : part1408_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1408 : List Witness := part1408_0
theorem accepted1408 : records1408.all (validRecord false fullProfiles)=true := by
  exact validpart1408_0
private noncomputable def part1440_0 : List Witness := witnesses% "794611562307954688,4458456175616,48,33,28,19,8,64,65,66"
private theorem validpart1440_0 : part1440_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1440 : List Witness := part1440_0
theorem accepted1440 : records1440.all (validRecord false fullProfiles)=true := by
  exact validpart1440_0
noncomputable def records1472 : List Witness := []
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1504 : List Witness := []
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket10_2
