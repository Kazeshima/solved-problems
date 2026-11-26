import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket06_2
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
private noncomputable def part1120_0 : List Witness := witnesses% "579849447148783840,60401275904,61,49,43,19,10,66,67,70;579849455738718432,60401144832,39,19,10,7,4,3,66,68,69,70;579849447148800224,60401144832,61,49,43,19,10,66,67,70;579849455738734816,60401143808,61,49,43,19,10,66,67,70"
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
private noncomputable def part1280_0 : List Witness := witnesses% "721422566494963744,60401275904,48,41,30,4,65,66;721422566494971936,60401144832,52,45,6,5,3,64,66,67,69"
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
private noncomputable def part1408_0 : List Witness := witnesses% "793480160532891680,60401144832,48,41,30,4,65,66;793480160532899872,60401143808,48,41,30,4,65,66"
private theorem validpart1408_0 : part1408_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1408 : List Witness := part1408_0
theorem accepted1408 : records1408.all (validRecord false fullProfiles)=true := by
  exact validpart1408_0
noncomputable def records1440 : List Witness := []
theorem accepted1440 : records1440.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1472 : List Witness := []
theorem accepted1472 : records1472.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1504 : List Witness := []
theorem accepted1504 : records1504.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket06_2
