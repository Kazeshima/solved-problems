import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket10_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "14311654729728,4458456175616,7,5,3,70"
private theorem validpart0_0 : part0_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records0 : List Witness := part0_0
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  exact validpart0_0
noncomputable def records32 : List Witness := []
theorem accepted32 : records32.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part64_0 : List Witness := witnesses% "2260657935767776,4458456175616,47,27,15,13,2,67,70;3096234705819648,4458456175616,27,24,7,5,67,68,70"
private theorem validpart64_0 : part64_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records64 : List Witness := part64_0
theorem accepted64 : records64.all (validRecord false fullProfiles)=true := by
  exact validpart64_0
private noncomputable def part96_0 : List Witness := witnesses% "3388694862530784,4458456175616,52,24,9,6,4,64,65,66,69"
private theorem validpart96_0 : part96_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records96 : List Witness := part96_0
theorem accepted96 : records96.all (validRecord false fullProfiles)=true := by
  exact validpart96_0
private noncomputable def part128_0 : List Witness := witnesses% "72063109599635456,4458456175616,51,32,21,17,1,65,66,70;72067507646146560,4458456175616,37,24,15,13,9,65,66,67,68,69;72071905691609088,4458456175616,44,27,11,7,5,64,68,70;72071905692624896,4458456175616,36,18,6,4,2,65,66,68,69;72071905692649472,4458456175616,49,32,28,19,1,65,66,69,70;72070806181029888,4458456175616,60,44,14,12,10,1,69;72071888512788480,4458456175616,63,54,19,14,12,64,65,67,68;72071905155786752,4458456175616,51,33,20,16,1,65,66,70;72071905424222208,4458456175616,55,19,18,6,4,2,66,67;72071905692657664,567408401208832,27,22,4,1,64,67,69;72071905701046272,4458456175616,60,18,14,12,8,64,65,68;72071906766399488,4458456175616,34,32,11,1,64,66,67,68;72071907840141312,4458456175616,39,24,7,5,66,67,68;72071909987624960,4458456175616,56,32,30,26,1,64,65,70;72071914282592256,4458456175616,61,24,14,12,8,64,66,69,70;72071940052396032,4458456175616,44,18,14,12,65,69,70;72071905692657696,4458456175616,55,46,14,12,8,1,65,66,67,68,69;72071905692657728,4458456175616,45,25,15,13,66,67,69,70;72071905692657792,4458456175616,63,31,28,5,4,64,65,66,68,69;72071905692661760,4458456175616,52,19,8,7,5,64,65,66,67,68,70;72071905692674048,4458456175616,55,54,6,4,2,65,66,67,70;72071905694754816,4458456175616,47,38,6,4,1,64,67,68,69;72071905696851968,4458456175616,61,36,14,12,8,1,64,67,69;72074104715913216,4458456175616,34,32,23,22,10,64,65,66,67,69;72353380669368320,4458456175616,63,17,11,6,4,3,64,65,66,68,69;72634855646078976,4458456175616,45,24,19,6,4,1,65,66,70;72902028930062336,4458456175616,18,8,6,4,65,69,70"
private theorem validpart128_0 : part128_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records128 : List Witness := part128_0
theorem accepted128 : records128.all (validRecord false fullProfiles)=true := by
  exact validpart128_0
private noncomputable def part160_0 : List Witness := witnesses% "73197805599500288,4458456175616,46,18,15,13,9,70"
private theorem validpart160_0 : part160_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records160 : List Witness := part160_0
theorem accepted160 : records160.all (validRecord false fullProfiles)=true := by
  exact validpart160_0
private noncomputable def part192_0 : List Witness := witnesses% "74323705506342912,4458456175616,51,43,30,26,22,64,65,67,70;74590878790326272,4458456175616,45,17,16,14,12,66,67;74872353767036928,4458456175616,43,41,37,31,1,65,67,68;75153828739553280,4458456175616,42,40,39,23,8,1,65,66,67,68,70;75153828743743488,4458456175616,63,36,17,7,5,1,64,65,66,67,68,70;75153820153812992,4458456175616,61,26,9,6,4,3,64,65,66,67,69;75153827670005760,4458456175616,43,41,22,8,2,65,66,67,68,70;75153828475312128,4458456175616,62,48,33,30,13,64,65,66,69;75153828735358976,4458456175616,47,27,8,7,5,66,67,68;75153828743747584,567408401208832,30,14,12,64,69;75153829280618496,4458456175616,49,48,26,25,9,1,64,65,66,67;75153830891231232,4458456175616,39,27,7,5,3,64,65,66,68,69;75153833038714880,4458456175616,59,35,30,26,1,64,65,66,68,70;75153845923616768,4458456175616,53,16,14,12,1,65,68,69,70;75153863103485952,4458456175616,56,35,19,11,5,4,64,65,67,69,70;75154928255375360,4458456175616,63,27,18,14,12,2,66,67,68;75153828743747616,4458456175616,52,45,14,12,66,69,70;75153828743747648,4458456175616,63,46,25,15,13,1,64,66,68;75153828743747712,4458456175616,63,7,5,64,65,66,67,69;75153828743755776,4458456175616,61,39,11,6,4,69;75153828743763968,4458456175616,61,17,16,15,13,9,65,66,69;75153828743780352,4458456175616,55,16,11,7,5,67,69;75153828744796160,4458456175616,44,24,16,7,5,3,64,65,66,67,68,70;75153828745844736,4458456175616,42,40,30,29,64,66,69,70;75156027767003136,4458456175616,63,46,36,15,13,64,65,66,67,68,70;75158226790258688,4458456175616,61,36,9,7,5,2,64,66,67,69,70;75162624836769792,4458456175616,52,44,18,6,4,2,65,69,70"
private theorem validpart192_0 : part192_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records192 : List Witness := part192_0
theorem accepted192 : records192.all (validRecord false fullProfiles)=true := by
  exact validpart192_0
private noncomputable def part224_0 : List Witness := witnesses% "76279728650590208,4458456175616,55,54,8,6,4,65,66,67,68,69"
private theorem validpart224_0 : part224_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records224 : List Witness := part224_0
theorem accepted224 : records224.all (validRecord false fullProfiles)=true := by
  exact validpart224_0
private noncomputable def part256_0 : List Witness := witnesses% "144975070890559520,4458456175616,59,56,24,5,4,68,69"
private theorem validpart256_0 : part256_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records256 : List Witness := part256_0
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  exact validpart256_0
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records320 : List Witness := []
theorem accepted320 : records320.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records352 : List Witness := []
theorem accepted352 : records352.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part384_0 : List Witness := witnesses% "216187093768513536,4458456175616,37,19,6,4,2,65,66,67,68,69;216465255997909152,4458456175616,60,24,7,5,3,64,65,67,69,70"
private theorem validpart384_0 : part384_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records384 : List Witness := part384_0
theorem accepted384 : records384.all (validRecord false fullProfiles)=true := by
  exact validpart384_0
noncomputable def records416 : List Witness := []
theorem accepted416 : records416.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part448_0 : List Witness := witnesses% "219269016819603456,4458456175616,37,16,10,7,5,1,67,68,70"
private theorem validpart448_0 : part448_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records448 : List Witness := part448_0
theorem accepted448 : records448.all (validRecord false fullProfiles)=true := by
  exact validpart448_0
noncomputable def records480 : List Witness := []
theorem accepted480 : records480.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket10_0
