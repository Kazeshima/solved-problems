import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket11_0
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
private noncomputable def part384_0 : List Witness := witnesses% "217022721057095680,4449857717248,54,20,1,66,67,69,70;217031532720431104,4449857848384,53,47,36,23,19,1,64,65,66,67,70;217033731743678464,4449857717248,20,9,1,64,65,67,69;217033731743686656,4449857721344,20,9,1,64,65,67,69;217033733891170304,4449857717248,63,45,20,15,1,65,67,68;217033766103425024,36509335552,42,39,25,23,5,66,69;217033731745783808,36509335552,44,33,13,3,64,67,68"
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
end Quadric.Five.Moves.RPacket11_0
