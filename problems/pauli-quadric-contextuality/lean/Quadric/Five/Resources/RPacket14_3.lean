import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket14_3
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable def records1536 : List Witness := []
theorem accepted1536 : records1536.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1568_0 : List Witness := witnesses% "865828637660824808,4449857848384,60,42,25,16,8,65"
private theorem validpart1568_0 : part1568_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1568 : List Witness := part1568_0
theorem accepted1568 : records1568.all (validRecord false fullProfiles)=true := by
  exact validpart1568_0
noncomputable def records1600 : List Witness := []
theorem accepted1600 : records1600.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1632_0 : List Witness := witnesses% "868080437474510024,60401143808,52,45,28,23,1,64,65,66,68;868080437474510056,4449857721344,63,19,9,4,3,2,69,70;868080437474514152,36509335552,48,15,9,2,1,65,67,68,69,70;868080437474542824,4449857717248,31,8,7,6,65,67"
private theorem validpart1632_0 : part1632_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1632 : List Witness := part1632_0
theorem accepted1632 : records1632.all (validRecord false fullProfiles)=true := by
  exact validpart1632_0
noncomputable def records1664 : List Witness := []
theorem accepted1664 : records1664.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1696 : List Witness := []
theorem accepted1696 : records1696.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1728 : List Witness := []
theorem accepted1728 : records1728.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1760 : List Witness := []
theorem accepted1760 : records1760.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1792 : List Witness := []
theorem accepted1792 : records1792.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1824_0 : List Witness := witnesses% "1009935029643658472,60401143808,41,34,29,9,1,66,67;1009943825736680616,36509335552,54,34,29,2,1,64,66,67,69,70;1009943817146746088,4449857717248,60,26,17,4,3,65,66,67,68,69;1009943825736680680,4449857721344,53,19,9,4,3,1,66,68,69,70"
private theorem validpart1824_0 : part1824_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1824 : List Witness := part1824_0
theorem accepted1824 : records1824.all (validRecord false fullProfiles)=true := by
  exact validpart1824_0
noncomputable def records1856 : List Witness := []
theorem accepted1856 : records1856.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1888_0 : List Witness := witnesses% "1012186829457343688,36509335552,45,33,30,2,1,65,66,68,69,70;1012186812277474536,4449857717248,46,26,18,4,2,66,68,69,70;1012186829457343720,4449857721344,60,50,26,6,65,68,70;1012195625550365864,4449857721344,54,35,20,14,3,67,70;1012195625550365896,4449857721344,36,26,18,4,68,69,70;1012196725061993672,4449857717248,36,26,18,4,68,69,70;1012195591190627560,4458447787200,55,46,28,15,64,67,70;1012195608370496744,4449857721344,60,16,10,4,2,1,65,66,68,69;1012195608378885352,4449857848384,41,17,12,7,2,70;1012195609444238568,60401143808,62,30,12,5,4,2,64,65,68,70;1012195616960431336,4449857721344,60,26,17,4,3,65,66,67,68,69;1012195617497302248,60401143808,61,29,20,6,4,1,64,65,67,70;1012195621255398632,4458447787200,63,46,43,14,65,67,69;1012195625550365928,567391220290560,23,12,5,68,70;1012195625558754536,4449857721344,63,54,26,4,65,66,68,69;1012195626087236840,4449857721344,42,30,21,12,8,64,69;1012195626095625448,36509335552,51,23,9,5,2,1,67,68;1012195626624107752,4449857721344,39,16,10,4,2,67,68,69;1012196707882124520,36509335552,48,39,26,22,8,7,66,68,69;1012196725061993704,4449857721344,54,36,26,4,1,65,66,68,69;1012196725598864616,4449857848384,56,53,27,11,2,66,69,70;1012195625550369960,4449857848384,50,15,6,1,65,67;1012195625550370024,4449857721344,50,39,26,6,1,65,66,68,70;1012195626624111848,4449857717248,39,16,10,4,2,67,68,69;1012195625550374120,4458447787200,50,33,10,64,65,66,68,69,70;1012195616960464104,4449857848384,50,29,20,4,1,64,65,67,68,69,70;1012195625550398696,4449857721344,49,20,14,6,3,1,68;1012195625558787304,60401143808,47,28,23,12,2,1,64,65,67,68,69,70;1012195626624140520,36509335552,43,29,15,6,2,1,67,68;1012195625551414472,4449857848384,59,55,37,17,10,1,65,66,68;1012195625551414504,4449857721344,53,26,18,4,3,66,68,69,70;1012195626088285416,4449857717248,53,26,18,4,3,66,68,69,70;1012195625551418600,60401143808,52,15,4,2,1,66,67,68;1012195625554560232,4458447787200,61,59,26,12,8,64,65,66,68,70;1012200023596877032,4458447787200,63,33,14,10,1,64,65,66,68,69;1012477100527076520,4449857717248,54,22,8,3,2,65,68,69,70;1012477091937141992,36509335552,40,39,25,16,13,7,66,67,69;1012477100527076584,4449857721344,49,26,21,6,3,67,68;1012477101600818408,4449857848384,61,59,52,22,18,1,66,67,69,70;1012478200038704360,60401143808,48,32,8,6,5,4,65,66,68,69,70;1012758575503787240,4458447787200,58,27,14,10,65,67,69"
private theorem validpart1888_0 : part1888_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1888 : List Witness := part1888_0
theorem accepted1888 : records1888.all (validRecord false fullProfiles)=true := by
  exact validpart1888_0
noncomputable def records1920 : List Witness := []
theorem accepted1920 : records1920.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1952 : List Witness := []
theorem accepted1952 : records1952.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1984 : List Witness := []
theorem accepted1984 : records1984.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part2016_0 : List Witness := witnesses% "1084253219588293864,4458447787200,45,40,13,7,3,64,67,69,70;1084535737715696872,4458447787200,63,46,43,14,1,65,67,69"
private theorem validpart2016_0 : part2016_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records2016 : List Witness := part2016_0
theorem accepted2016 : records2016.all (validRecord false fullProfiles)=true := by
  exact validpart2016_0
end Quadric.Five.Moves.RPacket14_3
