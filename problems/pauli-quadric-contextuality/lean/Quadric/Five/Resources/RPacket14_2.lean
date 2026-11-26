import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket14_2
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
noncomputable def records1280 : List Witness := []
theorem accepted1280 : records1280.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1312 : List Witness := []
theorem accepted1312 : records1312.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1344 : List Witness := []
theorem accepted1344 : records1344.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1376_0 : List Witness := witnesses% "723956453305631976,4449857848384,41,21,15,6,68;723965249398654120,60401143808,38,29,8,4,1,67,68;723965249398654184,4449857721344,63,26,18,4,1,67,68,69,70;723965249407042792,4449857717248,28,15,6,4,64,67,68;723965249399702760,36509335552,40,23,18,2,1,64,67,68,69,70"
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
end Quadric.Five.Moves.RPacket14_2
