import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket14_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "567958154925064,4458447787200,50,33,10,6,1,64,65,66;567958155969544,60401143808,52,20,8,6,5,66,69,70;567940976104456,4449857717248,45,26,4,3,2,65,66,67,69;567958155973640,4449857721344,49,26,6,3,67,68;567958155973672,36509335552,42,37,22,12,8,65,66,67,68,69;567958157005832,4458447787200,63,33,14,10,64,65,66,67,68,69;567949567083528,4449857717248,26,18,4,68,69,70;567958157018120,4449857721344,54,26,4,1,65,66,68,69;567958157018184,36509335552,49,38,20,16,13,64,66,67,68,69;567940977153032,4449857721344,19,9,7,6,5,70;567940985541640,36509335552,54,34,27,6,2,1,64,66,67,68,70;567942050894856,60401143808,38,36,29,8,4,1,65,66,68,69;567949567087624,4449857721344,26,18,4,68,69,70;567950103958536,60401143808,61,31,14,12,10,1,64,66,68;567957888586760,4458447787200,43,41,30,25,8,64,65,66,67,68,70;567958157022216,567391220290560,63,23,5,64,65,66,67,69,70;567958165410824,4449857721344,54,35,23,13,4,67,70;567958693893128,4449857721344,53,46,19,9,4,1,66,67,69,70;567958702281736,4449857848384,52,34,17,9,7,64,67;567959230764040,4449857721344,54,45,19,9,4,65,66,67,69,70;567960304505864,4458447787200,48,46,27,14,64,65,66,68,69;569040488780808,4449857848384,50,22,15,6,1,64,67,68,69;569057668649992,4449857721344,55,34,25,15,5,1,70;569058205520904,36509335552,48,20,15,9,2,1,64,67,68,69,70;567958157022248,4449857721344,55,47,14,12,6,1,64,65,68;567958165410856,4449857717248,39,21,17,11,2,65,68,70;567958157022280,4449857721344,42,30,12,8,1,64,67,69;567958157022344,4458447787200,56,46,43,64,66,67,69,70;567949567120392,36509335552,45,33,27,5,2,1,65,66,67,68,70;567958157054984,4449857721344,56,54,26,22,4,66,68,69,70;567958165443592,60401143808,47,27,13,9,6,1,64,66,67,68;567959230796808,4449857848384,58,55,21,17,65,66,67,68;567958157055048,4449857717248,53,28,11,9,2,64,67,68;570157180277768,4458447787200,55,22,15,5,66,67,68,69,70;576754250044424,4449857721344,54,17,16,10,4,66,67,68,69;576754786915336,4449857717248,54,17,16,10,4,66,67,68,69;576754250044456,4449857848384,50,31,11,4,2,1,65,67,68,69,70;849424543798280,4449857848384,40,37,19,14,10,1,65,66,68;849433133732872,4449857721344,62,47,25,11,4,64,65,66,67,68,69,70;849434207474696,36509335552,40,27,18,12,2,1,65,67,68,69,70;850532645360648,60401143808,52,36,15,4,2,1,64,67,69"
private theorem validpart0_0 : part0_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records0 : List Witness := part0_0
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  exact validpart0_0
private noncomputable def part32_0 : List Witness := witnesses% "1693858063864840,4458447787200,56,48,25,7,2,64,65,67,68,69,70"
private theorem validpart32_0 : part32_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records32 : List Witness := part32_0
theorem accepted32 : records32.all (validRecord false fullProfiles)=true := by
  exact validpart32_0
private noncomputable def part64_0 : List Witness := witnesses% "2819757970707464,4449857721344,63,54,36,26,4,65,68,69;2819759044449288,4449857717248,36,28,15,6,4,64,65,66;2819757970707528,4449857848384,56,53,12,7,2,65,66,68,69,70;2828554063729672,60401143808,56,51,12,2,1,65,66,68,69,70"
private theorem validpart64_0 : part64_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records64 : List Witness := part64_0
theorem accepted64 : records64.all (validRecord false fullProfiles)=true := by
  exact validpart64_0
noncomputable def records96 : List Witness := []
theorem accepted96 : records96.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records128 : List Witness := []
theorem accepted128 : records128.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records160 : List Witness := []
theorem accepted160 : records160.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records192 : List Witness := []
theorem accepted192 : records192.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records224 : List Witness := []
theorem accepted224 : records224.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part256_0 : List Witness := witnesses% "144683146232873992,4449857848384,41,27,17,11,2,70;144683146232878088,4449857721344,62,61,18,11,4,1,65,66,68,69;144683146232878120,60401143808,58,35,13,5,1,64,65,66,67,68,70;144964621209588744,4449857717248,62,47,25,11,4,64,65,66,67,68,69,70"
private theorem validpart256_0 : part256_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records256 : List Witness := part256_0
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  exact validpart256_0
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part320_0 : List Witness := witnesses% "146934946046563336,36509335552,51,9,5,2,1,67,68"
private theorem validpart320_0 : part320_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records320 : List Witness := part320_0
theorem accepted320 : records320.all (validRecord false fullProfiles)=true := by
  exact validpart320_0
noncomputable def records352 : List Witness := []
theorem accepted352 : records352.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records384 : List Witness := []
theorem accepted384 : records384.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records416 : List Witness := []
theorem accepted416 : records416.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records448 : List Witness := []
theorem accepted448 : records448.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records480 : List Witness := []
theorem accepted480 : records480.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket14_0
