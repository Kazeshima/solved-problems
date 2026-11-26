import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket06_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "567408401209344,60401275904,34,33,21,15,64,66,68,69;567408401209408,60401144832,58,57,20,13,3,64,66,67,69"
private theorem validpart0_0 : part0_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records0 : List Witness := part0_0
theorem accepted0 : records0.all (validRecord false fullProfiles)=true := by
  exact validpart0_0
noncomputable def records32 : List Witness := []
theorem accepted32 : records32.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part64_0 : List Witness := witnesses% "2819208214894592,60401144832,34,33,21,15,64,66,68,69;2819208214894656,60401143808,34,33,21,15,64,66,68,69"
private theorem validpart64_0 : part64_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records64 : List Witness := part64_0
theorem accepted64 : records64.all (validRecord false fullProfiles)=true := by
  exact validpart64_0
noncomputable def records96 : List Witness := []
theorem accepted96 : records96.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part128_0 : List Witness := witnesses% "72071905675487232,60401275904,52,45,36,7,4,64,69,70;72071907822970880,60401144832,52,45,36,7,4,64,69,70;72353380652197888,60401144832,50,40,39,19,10,64,65,68,70;72353382799681536,60401143808,52,45,36,7,4,64,69,70"
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
noncomputable def records256 : List Witness := []
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records320 : List Witness := []
theorem accepted320 : records320.all (validRecord false fullProfiles)=true := by
  rfl
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
end Quadric.Five.Moves.RPacket06_0
