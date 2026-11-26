import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket09_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records0 : List Witness := []
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  rfl
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
private noncomputable def part192_0 : List Witness := witnesses% "75153828727226368,4449857852424,52,51,25,14,12,65,66,69;75153828727230464,4458447787016,59,44,38,5,1,65,66,69,70;75153830874714112,4449857852424,59,44,38,5,1,65,66,69,70;75154928238858240,4449857852424,57,44,28,24,4,2,64,66,67,68,69,70;75154930386341888,4450394723336,59,44,38,5,1,65,66,69,70"
private theorem validpart192_0 : part192_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records192 : List Witness := part192_0
theorem accepted192 : records192.all (validRecord false fullProfiles)=true := by
  exact validpart192_0
noncomputable def records224 : List Witness := []
theorem accepted224 : records224.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part256_0 : List Witness := witnesses% "144975070874042400,4449857852424,59,44,38,31,5,1,65,66,69,70;144975070874046496,4450394723336,59,44,38,31,5,1,65,66,69,70"
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
private noncomputable def part384_0 : List Witness := witnesses% "217024970482257920,60401143808,43,20,17,14,64,65,68,69,70"
private theorem validpart384_0 : part384_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records384 : List Witness := part384_0
theorem accepted384 : records384.all (validRecord false fullProfiles)=true := by
  exact validpart384_0
noncomputable def records416 : List Witness := []
theorem accepted416 : records416.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records448 : List Witness := []
theorem accepted448 : records448.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records480 : List Witness := []
theorem accepted480 : records480.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket09_0
