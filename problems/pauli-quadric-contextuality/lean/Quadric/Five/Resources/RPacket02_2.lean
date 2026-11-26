import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket02_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part1024_0 : List Witness := witnesses% "576476163194529000,283540423974912,47,27,14,10,2,1,69;576476163462964456,4432677983232,51,31,18,9,1,64,65,67,69,70"
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
noncomputable def records1120 : List Witness := []
theorem accepted1120 : records1120.all (validRecord false fullProfiles)=true := by
  rfl
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
private noncomputable def part1280_0 : List Witness := witnesses% "720586987575182504,4449857852480,62,31,8,5,1,64,65,66,67,69,70;720586987583571112,4449857848384,62,31,8,5,1,64,65,66,67,69,70;720591385621693608,567356870022144,62,61,22,15,11,65,69,70"
private theorem validpart1280_0 : part1280_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1280 : List Witness := part1280_0
theorem accepted1280 : records1280.all (validRecord false fullProfiles)=true := by
  exact validpart1280_0
noncomputable def records1312 : List Witness := []
theorem accepted1312 : records1312.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1344 : List Witness := []
theorem accepted1344 : records1344.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1376_0 : List Witness := witnesses% "723964699642709160,4450394723336,57,32,31,27,2,64,65,66,67,68;723964691052774632,567356870022144,35,30,29,14,10,8,65,67,68;723964695347741928,567356870022144,50,33,14,12,65,66,68;723964699642709224,567374049891328,50,33,14,12,65,66,68;723964700716451048,567356870022144,50,33,28,20,6,65,66,69,70;723964699643757800,4450394723336,53,26,18,4,3,66,68,69,70"
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
private noncomputable def part1472_0 : List Witness := witnesses% "795740768248530088,4449857852424,62,36,19,18,10,4,64,68,69;795740768250627240,4450394723336,63,45,30,11,3,1,65"
private theorem validpart1472_0 : part1472_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1472 : List Witness := part1472_0
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  exact validpart1472_0
private noncomputable def part1504_0 : List Witness := witnesses% "796303718197757096,283540423974912,54,42,29,19,4,64,65,66;796303718201951400,4458447782976,55,47,20,13,11,64,66,70;796303718738822312,4449857848384,55,47,20,13,11,64,66,70;796304817713579176,567356870022144,42,22,18,1,64,65,68,69,70;796303718201951464,283540423974912,45,18,15,5,65,67,68,70;796303718204048552,567356870022144,55,48,21,10,7,2,64,66,68;796857872062350504,4432677983232,52,24,16,4,3,65,69,70;796857872062354600,283540423974912,56,18,10,64,65,69;796866668151178408,4432677983232,45,17,9,4,3,65,67,69,70;796866668155372712,4458447787072,37,30,12,64,65,67,70;796866668692243624,4449857852480,55,47,20,13,11,64,66,70;796866670302856360,4449857852424,59,23,9,7,5,2,65,68,70;796866685335241896,4449857852424,55,40,20,16,13,5,64,65,66,67,69,70;796867767667000488,567374049891328,35,34,22,18,9,64,65,68,69,70;796867768203871400,567356870022144,62,56,22,3,2,64,65,67,68,69,70;796867769814484136,4450394723336,34,32,9,64,66,69,70;796866668155372776,4432677983232,58,38,31,18,64,65,67,68,69;796866668155376808,4458447782976,37,30,12,64,65,67,70;796867767667004584,567356870022144,45,42,22,5,1,65,66,67;796866668155405480,4449857852424,39,36,17,16,9,4,68,69;796867767667033256,4450394723336,47,23,14,7,3,1,65;796866668157469864,567374049891328,60,20,11,5,2,65,67,70;796866685337339048,4450394723336,63,27,15,13,11,64,65,68,69,70;796866668157473960,567356870022144,42,29,23,10,5,64,70"
private theorem validpart1504_0 : part1504_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1504 : List Witness := part1504_0
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  exact validpart1504_0
end Quadric.Five.Moves.RPacket02_2
