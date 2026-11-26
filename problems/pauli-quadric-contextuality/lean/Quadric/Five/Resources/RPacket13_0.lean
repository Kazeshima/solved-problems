import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket13_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "567958156891144,4458447787200,38,31,13,9,1,65,67,68,69"
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
noncomputable def records256 : List Witness := []
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records320 : List Witness := []
theorem accepted320 : records320.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part352_0 : List Witness := witnesses% "148348923100026024,4458447787200,25,23,10,6,5,65,67,70"
private theorem validpart352_0 : part352_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records352 : List Witness := part352_0
theorem accepted352 : records352.all (validRecord false fullProfiles)=true := by
  exact validpart352_0
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
end Quadric.Five.Moves.RPacket13_0
