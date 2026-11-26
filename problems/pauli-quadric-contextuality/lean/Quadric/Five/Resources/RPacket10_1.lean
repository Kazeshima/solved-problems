import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket10_1
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records512 : List Witness := []
theorem accepted512 : records512.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records544 : List Witness := []
theorem accepted544 : records544.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records576 : List Witness := []
theorem accepted576 : records576.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part608_0 : List Witness := witnesses% "292176588094101568,4458456175616,35,32,24,5,4,66,69"
private theorem validpart608_0 : part608_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records608 : List Witness := part608_0
theorem accepted608 : records608.all (validRecord false fullProfiles)=true := by
  exact validpart608_0
private noncomputable def part640_0 : List Witness := witnesses% "360302281844369408,4458456175616,38,26,17,6,4,1,67,68,70"
private theorem validpart640_0 : part640_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records640 : List Witness := part640_0
theorem accepted640 : records640.all (validRecord false fullProfiles)=true := by
  exact validpart640_0
noncomputable def records672 : List Witness := []
theorem accepted672 : records672.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part704_0 : List Witness := witnesses% "363384204895459328,4458456175616,54,49,42,25,10,64,69"
private theorem validpart704_0 : part704_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records704 : List Witness := part704_0
theorem accepted704 : records704.all (validRecord false fullProfiles)=true := by
  exact validpart704_0
private noncomputable def part736_0 : List Witness := witnesses% "363666773201451200,4458456175616,60,27,7,5,67,68,70"
private theorem validpart736_0 : part736_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records736 : List Witness := part736_0
theorem accepted736 : records736.all (validRecord false fullProfiles)=true := by
  exact validpart736_0
noncomputable def records768 : List Witness := []
theorem accepted768 : records768.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records800 : List Witness := []
theorem accepted800 : records800.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records832 : List Witness := []
theorem accepted832 : records832.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records864 : List Witness := []
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part896_0 : List Witness := witnesses% "505253149229479936,4458456175616,55,19,9,6,4,1,65,66,68,69"
private theorem validpart896_0 : part896_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records896 : List Witness := part896_0
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  exact validpart896_0
private noncomputable def part928_0 : List Witness := witnesses% "506381186156242944,4458456175616,44,24,9,6,4,64,67,68,70"
private theorem validpart928_0 : part928_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records928 : List Witness := part928_0
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  exact validpart928_0
noncomputable def records960 : List Witness := []
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records992 : List Witness := []
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket10_1
