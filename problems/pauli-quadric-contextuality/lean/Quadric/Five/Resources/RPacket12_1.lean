import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket12_1
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
private noncomputable def part576_0 : List Witness := witnesses% "290482769744646344,567382631404552,63,54,18,4,64,66,68,69,70"
private theorem validpart576_0 : part576_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records576 : List Witness := part576_0
theorem accepted576 : records576.all (validRecord false fullProfiles)=true := by
  exact validpart576_0
private noncomputable def part608_0 : List Witness := witnesses% "291608669651484872,567382631404552,60,10,8,4,1,66,69;291608669651488968,567391758210048,61,40,5,2;291609769163116744,567382631404552,55,27,8,4,65,69,70;291608669651521736,567382631404552,52,45,27,4,2,64,65,66,69,70;291608669653586120,567382631404552,46,27,10,4,65,66,68,69,70;291608669655683272,567382631404552,46,44,18,4,1,69;291617465744511176,567382631404552,63,17,16,4,64,66,67,69;292171619604910280,567382631404552,53,52,11,4,64,66,67,69"
private theorem validpart608_0 : part608_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records608 : List Witness := part608_0
theorem accepted608 : records608.all (validRecord false fullProfiles)=true := by
  exact validpart608_0
private noncomputable def part640_0 : List Witness := witnesses% "360571098196090888,567382631404552,37,25,4,2,66,69"
private theorem validpart640_0 : part640_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records640 : List Witness := part640_0
theorem accepted640 : records640.all (validRecord false fullProfiles)=true := by
  exact validpart640_0
noncomputable def records672 : List Witness := []
theorem accepted672 : records672.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part704_0 : List Witness := witnesses% "363399104645042184,567382631404552,37,26,4,1,68,69,70"
private theorem validpart704_0 : part704_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records704 : List Witness := part704_0
theorem accepted704 : records704.all (validRecord false fullProfiles)=true := by
  exact validpart704_0
noncomputable def records736 : List Witness := []
theorem accepted736 : records736.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records768 : List Witness := []
theorem accepted768 : records768.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part800_0 : List Witness := witnesses% "434324201975857160,567382631404552,55,27,10,4,65,66,68,69"
private theorem validpart800_0 : part800_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records800 : List Witness := part800_0
theorem accepted800 : records800.all (validRecord false fullProfiles)=true := by
  exact validpart800_0
noncomputable def records832 : List Witness := []
theorem accepted832 : records832.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records864 : List Witness := []
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part896_0 : List Witness := witnesses% "504686285198204936,567382631404552,37,36,26,4,1,66,68,69,70;504686285735075848,567382631404552,39,37,25,4,1,66,68,69,70;504686286271946760,567391758210048,42,22,18,3,65,68,69,70;504686290566914056,567382631404552,60,36,4,2,1,66,69;504686320631685128,567382631404552,63,36,26,25,4,69;504686286271946888,567382631404552,60,4,3,67,68,69,70"
private theorem validpart896_0 : part896_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records896 : List Witness := part896_0
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  exact validpart896_0
noncomputable def records928 : List Witness := []
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records960 : List Witness := []
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records992 : List Witness := []
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket12_1
