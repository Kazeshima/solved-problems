import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket12_0
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part0_0 : List Witness := witnesses% "567898032603144,567382631404552,27,4,64,65,69,70"
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
private noncomputable def part192_0 : List Witness := witnesses% "75168694133592072,567382631404552,60,36,4,3,67,68,69,70;75168724198363144,567382631404552,63,36,4,64,65,66,69,70;75168727419588616,567382631404552,63,53,16,4,64,66,67,69;75168727956459528,567382631404552,63,46,8,4,65,66,68,69;75168728493330440,567391758210048,33,21,11,7,64,67;75168728493330568,567382631404552,63,26,25,4,66,69"
private theorem validpart192_0 : part192_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records192 : List Witness := part192_0
theorem accepted192 : records192.all (validRecord false fullProfiles)=true := by
  exact validpart192_0
noncomputable def records224 : List Witness := []
theorem accepted224 : records224.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part256_0 : List Witness := witnesses% "144124586004316328,567382631404552,63,45,9,4,65,66,67,69,70;144126785026523304,567382631404552,60,17,16,4,2,66,69;144126785027571880,567391758210048,51,26,5,1,65,67,69,70;144126785035960488,567382631404552,54,44,27,4,1,64,65,66,69,70;144126785027580072,567382631404552,53,52,9,4,2,69;144126785027588264,567382631404552,53,27,17,4,64,66,67,69,70;144131183074082984,567382631404552,46,44,19,4,65,66,68,69;144408260004282536,567382631404552,47,16,11,4,64,69,70"
private theorem validpart256_0 : part256_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records256 : List Witness := part256_0
theorem accepted256 : records256.all (validRecord false fullProfiles)=true := by
  exact validpart256_0
noncomputable def records288 : List Witness := []
theorem accepted288 : records288.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part320_0 : List Witness := witnesses% "146378584841257128,567382631404552,63,10,8,4,65,66,68,69"
private theorem validpart320_0 : part320_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records320 : List Witness := part320_0
theorem accepted320 : records320.all (validRecord false fullProfiles)=true := by
  exact validpart320_0
noncomputable def records352 : List Witness := []
theorem accepted352 : records352.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part384_0 : List Witness := witnesses% "216455910120235016,567382631404552,38,26,4,1,66,69"
private theorem validpart384_0 : part384_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records384 : List Witness := part384_0
theorem accepted384 : records384.all (validRecord false fullProfiles)=true := by
  exact validpart384_0
noncomputable def records416 : List Witness := []
theorem accepted416 : records416.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part448_0 : List Witness := witnesses% "219283916569186312,567382631404552,38,25,4,2,67,69,70"
private theorem validpart448_0 : part448_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records448 : List Witness := part448_0
theorem accepted448 : records448.all (validRecord false fullProfiles)=true := by
  exact validpart448_0
noncomputable def records480 : List Witness := []
theorem accepted480 : records480.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket12_0
