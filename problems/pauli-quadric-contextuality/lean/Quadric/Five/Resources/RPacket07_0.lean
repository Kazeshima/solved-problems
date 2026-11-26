import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket07_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "4458447789056,4458447787016,14,12,10,64,70;4458447789120,4449857852424,40,23,18,14,12,10,64,65,67;13254540811264,4449857852424,14,12,10,64,70;563010354699264,4458448311296,27,24,3;567408399113216,4441267917824,58,57,20,13,3,64,66,67,69;567408399145984,4432677983232,58,57,20,13,3,64,66,67,69;567408400161792,4458447787016,63,23,5,64,65,66,67,69,70;567408401193984,2251136434344,50,38,22,18;567408401206272,4441267917824,54,29,23,5,3,66,68,69,70;567408401206336,4441267916800,54,29,23,5,3,66,68,69,70;567374041472000,2251136434344,33,30,26,10,4,64,65,67,70;567391221341184,4458456175616,46,23,15,9,3,64,68,69,70;567399811275776,4441267917824,45,33,29,6,5,3,65,66,68,70;567408132774912,4458447787520,51,30,17,14,12,64,67,68,69,70;567408401210368,4458447787008,63,23,5,64,65,66,67,69,70;567408409598976,4458456175616,63,23,5,64,65,66,67,69,70;567408938081280,60401275904,46,23,13,3;567409474952192,4449857852416,40,23,18,65,67,69,70;567410011823104,60401144832,46,25,13,2,1,68;567410548694016,2251136434344,51,39,4,3,2,67,68;567412696177664,4458447787016,46,23,13,3;568507912838144,60401275904,63,25,13,7,1,64,66,67,69;567408401210400,4458447787016,37,31,12,10,64,65,67;567408401210432,4449857852416,46,23,15,9,3,64,68,69,70;567409474952256,4449857851392,46,23,15,9,3,64,68,69,70;567408401210464,4449857852424,46,23,15,9,3,64,68,69,70;567408401210496,4458448311296,46,23,13,3;567408401218560,4441267917824,57,30,11,5;567399811308544,4432677983232,45,33,29,6,5,3,65,66,68,70;567408401243136,4449857852416,58,57,20,13,3,64,66,67,69;567409474984960,4450394723328,40,23,18,65,67,69,70;568507912870912,60401144832,63,25,13,7,1,64,66,67,69;567408401243200,4449857721344,58,57,20,13,3,64,66,67,69;567409474985024,36509335552,59,32,23,13,4,65,66,68,69;567408401251328,4441267916800,57,30,11,5;567408405404672,2251136434344,33,21,20,15,1,65,68,69,70;569607424465920,4458447787520,58,57,20,13,3,64,66,67,69;576204494228480,4432677983232,62,59,24,23,3,2,64,65,66,69,70;576204494232576,4458447787072,40,23,18,65,67,69,70;576205031103488,4458447787200,53,52,24,12,64,65,66,67;576205567974400,4449857852480,40,23,18,65,67,69,70;576204494232608,4449857852424,37,31,12,10,64,65,67;576204494232640,4449857852480,37,28,15,9,6,64,67,68,69;576204494265344,4449857852480,45,42,19,14,67,68,69;848883377921024,4441267917824,40,23,18,65,67,69,70;848884451662848,4432677983232,40,23,18,65,67,69,70"
private theorem validpart0_0 : part0_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records0 : List Witness := part0_0
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  exact validpart0_0
private noncomputable def part32_0 : List Witness := witnesses% "1693308308052992,4458448311296,52,51,27,3,65,66,67,68,69,70"
private theorem validpart32_0 : part32_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records32 : List Witness := part32_0
theorem accepted32 : records32.all (validRecord false fullProfiles)=true := by
  exact validpart32_0
private noncomputable def part64_0 : List Witness := witnesses% "2819208212798464,4441267916800,58,57,20,13,3,64,66,67,69;2819208213847040,4449857852424,63,23,5,64,65,66,67,69,70;2819208214895616,4449857852416,63,23,5,64,65,66,67,69,70;2819209288637440,4449857721344,54,29,23,14,7,1,66,68;2819212509862912,4449857852424,41,37,21,13,11,2,64,65;2819208214895680,4449857721344,63,23,5,64,65,66,67,69,70;2819209288637504,4449857717248,63,23,5,64,65,66,67,69,70;2819208214928384,4449857851392,63,23,5,64,65,66,67,69,70;2819209288670208,36509335552,44,38,29,13,2,1,68;2819208214928448,4449857717248,46,23,15,9,3,64,68,69,70;2828004307917824,4458447782976,40,23,18,65,67,69,70;2828005381659648,4449857848384,40,23,18,65,67,69,70;2828004307917888,4449857848384,37,28,15,9,6,64,67,68,69"
private theorem validpart64_0 : part64_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records64 : List Witness := part64_0
theorem accepted64 : records64.all (validRecord false fullProfiles)=true := by
  exact validpart64_0
noncomputable def records96 : List Witness := []
theorem accepted96 : records96.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part128_0 : List Witness := witnesses% "72625002439138304,4441267917824,46,23,13,3;72625003512880128,4441267916800,46,23,13,3;72633798532160512,4432677983232,50,47,31,27,8,1,67;72907519492799488,4449857852424,53,17,14,12,10,65,67,69,70;72907520558152704,4449857852424,61,49,20,11,2,65,66,67;72907520566541312,4458447787016,61,49,20,11,2,65,66,67"
private theorem validpart128_0 : part128_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records128 : List Witness := part128_0
theorem accepted128 : records128.all (validRecord false fullProfiles)=true := by
  exact validpart128_0
noncomputable def records160 : List Witness := []
theorem accepted160 : records160.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records192 : List Witness := []
theorem accepted192 : records192.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records224 : List Witness := []
theorem accepted224 : records224.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part256_0 : List Witness := witnesses% "144682596477066240,4441267917824,58,57,20,15,9,3,64,66,67,70"
private theorem validpart256_0 : part256_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records256 : List Witness := part256_0
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  exact validpart256_0
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part320_0 : List Witness := witnesses% "146934396290751488,4441267916800,58,57,20,15,9,3,64,66,67,70"
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
end Quadric.Five.Moves.RPacket07_0
