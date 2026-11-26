import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket02_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "11047195903144,4449857852424,55,40,29,25,9,65,66,69,70;15445242414248,4450394723336,15,13,11,67,70;567408400028680,4432677983232,45,26,4,3,2,65,66,67,69;567391221208072,4449857852424,56,37,29,6,5,64,65,66,67,69;567392294949896,4450394723336,61,25,6,4,64,65,66,67,69;567399811142664,567374049891328,42,34,20,16,2,65,69;567400348013576,4450394723336,34,32,2,66,68;567401958626312,567356870022144,53,51,20,9,3,64,66,67,69;567408401077256,4458447787072,44,21,12,5,2,66;567408937948168,4449857852424,57,28,7,5,67,69;567409474819080,567374049891328,55,22,11,9,5,64,66,67,68,69;567410548560904,4449857852480,53,40,24,13,3,64,66,67,68;567399811142696,567356870022144,47,33,24,9,7,1,65,67,70;567408401077288,4458447782976,44,21,12,5,2,66;567409474819112,567356870022144,55,23,10,8,5,1,64,66,69;567408401077320,4432677983232,49,38,29,16,9,2,64,66,70;567399811175432,4450394723336,47,28,14,3,2,1,64,65,66,67,68,69,70;567408401110024,4449857852424,46,36,26,18,4,2,68,69,70;576204494099464,4432677983232,54,17,16,10,4,66,67,68,69;576204494099496,283540423974912,51,25,10,2,67,68,70;848883377787912,4449857852424,62,47,25,11,4,64,65,66,67,68,69,70;848884451529736,4450394723336,62,47,25,11,4,64,65,66,67,68,69,70"
private theorem validpart0_0 : part0_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records0 : List Witness := part0_0
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  exact validpart0_0
noncomputable def records32 : List Witness := []
theorem accepted32 : records32.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records64 : List Witness := []
theorem accepted64 : records64.all (validRecord false fullProfiles)=true := by
  rfl
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
private noncomputable def part256_0 : List Witness := witnesses% "144124036248503464,4432677983232,54,36,24,10,4,3,64,66,68,69,70;144124036248519848,283540423974912,54,42,8,6,4,65,66;144126235270710440,4449857852424,60,17,16,4,2,66,69;144126234734888104,4432677983232,61,33,29,25,16,2,64,65,66,67,68,69;144126235271759016,4458447787072,62,31,15,11,65,66,67,68,69;144126235280147624,4458447782976,62,31,15,11,65,66,67,68,69;144126239566726312,4449857852424,49,42,32,23,9,1,64,66,67,69,70;144126235271759080,4449857852480,39,31,14,3,1,69,70;144126235271767208,4449857852424,53,52,9,4,2,69;144126234734904488,283540423974912,54,36,12,10,3,64,65,66,67,69,70;144126235271775400,4458447782976,39,31,14,3,1,69,70;144126235271775464,4449857848384,39,31,14,3,1,69,70;144130633318270120,567374049891328,62,61,22,15,11,65,69,70;144130633326658728,567356870022144,34,33,29,25,13,65,67,68,70;144130633318278312,4450394723336,53,52,9,4,2,69;144130633318286504,567356870022144,53,50,26,11,9,1,65,67,69;144407710248469672,4432677983232,47,24,11,4,3,64,67,68,69,70;144407710256858280,283540423974912,56,13,7,3,64,68,69;144682596476933128,4432677983232,51,26,12,4,3,2,64,65,70;144682596476933160,283540423974912,54,16,15,5,66,69;144959659452683304,4450394723336,49,42,32,23,9,64,66,69,70;144959659461071912,4449857852424,49,42,32,23,9,64,66,69,70"
private theorem validpart256_0 : part256_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records256 : List Witness := part256_0
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  exact validpart256_0
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part320_0 : List Witness := witnesses% "146378035084395688,4450394723336,60,17,16,4,2,66,69;146378035085444264,567374049891328,50,40,11,7,65,66,67,68,69,70;146378035093832872,567356870022144,50,40,28,19,7,64,65,66,67,68;146378039380411560,4450394723336,57,32,31,27,9,65,67,70;146378035085444328,567356870022144,50,40,11,7,65,66,67,68,69,70;146378035085460648,567356870022144,58,32,11,7,2,1,65,66,67,68,69,70"
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
private noncomputable def part448_0 : List Witness := witnesses% "219280068024734888,4450394723336,63,27,6,4,64,65,66,67,68,69;219280068293170344,4449857852424,57,28,7,4,1,67,69"
private theorem validpart448_0 : part448_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records448 : List Witness := part448_0
theorem accepted448 : records448.all (validRecord false fullProfiles)=true := by
  exact validpart448_0
private noncomputable def part480_0 : List Witness := witnesses% "220405915851949224,4432677983232,62,53,51,26,12,2,64,65,67;220405915851953320,283540423974912,52,23,12,10,1,65,69,70"
private theorem validpart480_0 : part480_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records480 : List Witness := part480_0
theorem accepted480 : records480.all (validRecord false fullProfiles)=true := by
  exact validpart480_0
end Quadric.Five.Moves.RPacket02_0
