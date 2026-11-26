import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket09_2
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records1024 : List Witness := []
theorem accepted1024 : records1024.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1056 : List Witness := []
theorem accepted1056 : records1056.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1088 : List Witness := []
theorem accepted1088 : records1088.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1120_0 : List Witness := witnesses% "579847248126181600,4449857852424,60,41,21,8,2,1,64,66,67,68,69,70;579847249199923424,4450394723336,58,45,38,8,5,65,67,69,70;579849447149437152,4458447787016,52,51,24,12,3,65,66,67,68,69;579849448223178976,4449857852424,58,45,38,8,5,65,67,69,70;579849447149445344,4449857852424,52,51,24,12,3,65,66,67,68,69"
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
private noncomputable def part1216_0 : List Witness := witnesses% "651614581030649856,4450394723336,35,29,16,12,10,65,68,69;651614581030653952,4449857852424,35,29,16,12,10,65,68,69"
private theorem validpart1216_0 : part1216_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1216 : List Witness := part1216_0
theorem accepted1216 : records1216.all (validRecord false fullProfiles)=true := by
  exact validpart1216_0
private noncomputable def part1248_0 : List Witness := witnesses% "652741573738266624,60401143808,59,52,27,5,1,64,65,66,68,69,70"
private theorem validpart1248_0 : part1248_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1248 : List Witness := part1248_0
theorem accepted1248 : records1248.all (validRecord false fullProfiles)=true := by
  exact validpart1248_0
private noncomputable def part1280_0 : List Witness := witnesses% "721435823177465888,4458447787016,45,42,16,12,5,68;721435825324949536,4449857852424,35,27,17,10,6,1,65,67;721436922689093664,4449857852424,45,42,16,12,5,68;721436924836577312,4450394723336,45,42,16,12,5,68;721435823177469984,4449857852424,57,44,25,7,6,3,65,66,68,70"
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
noncomputable def records1376 : List Witness := []
theorem accepted1376 : records1376.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1408_0 : List Witness := witnesses% "793483473293410304,60401143808,56,26,17,12,3,67"
private theorem validpart1408_0 : part1408_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1408 : List Witness := part1408_0
theorem accepted1408 : records1408.all (validRecord false fullProfiles)=true := by
  exact validpart1408_0
private noncomputable def part1440_0 : List Witness := witnesses% "794611562291429376,4450394723336,49,30,8,7,6,4,65,70;794611562291437568,4449857852424,49,30,8,7,6,4,65,70"
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
end Quadric.Five.Moves.RPacket09_2
