import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket12_3
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records1536 : List Witness := []
theorem accepted1536 : records1536.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1568 : List Witness := []
theorem accepted1568 : records1568.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1600 : List Witness := []
theorem accepted1600 : records1600.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1632 : List Witness := []
theorem accepted1632 : records1632.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1664 : List Witness := []
theorem accepted1664 : records1664.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1696_0 : List Witness := witnesses% "937891686841884872,567382631404552,44,19,8,4,65,69,70"
private theorem validpart1696_0 : part1696_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1696 : List Witness := part1696_0
theorem accepted1696 : records1696.all (validRecord false fullProfiles)=true := by
  exact validpart1696_0
noncomputable def records1728 : List Witness := []
theorem accepted1728 : records1728.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1760_0 : List Witness := witnesses% "940139088609059016,567382631404552,63,46,10,4,65,66,68,69,70;940141287632314568,567382631404552,53,24,9,4,2,1,66,69;940143486655561928,567382631404552,54,27,18,4,64,68,69,70;940143486655570120,567391758210048,62,41,5,1,64,65,66,67,69,70;940143486663958728,567382631404552,63,36,10,8,4,65,66,68,69;940143486655586504,567382631404552,53,47,27,4,64,67,69;940143486656618696,567382631404552,47,45,16,4,2,67,69,70;940424961632280776,567382631404552,17,16,11,4,64,67,69"
private theorem validpart1760_0 : part1760_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1760 : List Witness := part1760_0
theorem accepted1760 : records1760.all (validRecord false fullProfiles)=true := by
  exact validpart1760_0
noncomputable def records1792 : List Witness := []
theorem accepted1792 : records1792.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1824_0 : List Witness := witnesses% "1009934967379124456,567382631404552,60,4,2,1,66,69;1010784937099411464,567382631404552,61,27,4,2,64,65,69,70;1010784945689346056,567382631404552,62,27,4,1,64,65,69,70;1010784952131797000,567382631404552,36,27,4,64,65,69,70;1010784954279280648,567391758210048,33,18,13,1,64,65,69,70;1010784954547716104,567382631404552,39,24,4,67,68,69,70;1010784954279280680,567382631404552,53,16,11,4,64,67,69;1010784954279280712,567382631404552,46,27,8,4,65,68,69"
private theorem validpart1824_0 : part1824_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1824 : List Witness := part1824_0
theorem accepted1824 : records1824.all (validRecord false fullProfiles)=true := by
  exact validpart1824_0
noncomputable def records1856 : List Witness := []
theorem accepted1856 : records1856.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1888 : List Witness := []
theorem accepted1888 : records1888.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1920 : List Witness := []
theorem accepted1920 : records1920.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1952_0 : List Witness := witnesses% "1082842548317208584,567382631404552,24,4,2,1,69"
private theorem validpart1952_0 : part1952_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1952 : List Witness := part1952_0
theorem accepted1952 : records1952.all (validRecord false fullProfiles)=true := by
  exact validpart1952_0
noncomputable def records1984 : List Witness := []
theorem accepted1984 : records1984.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records2016 : List Witness := []
theorem accepted2016 : records2016.all (validRecord false fullProfiles)=true := by
  rfl
end Quadric.Five.Moves.RPacket12_3
