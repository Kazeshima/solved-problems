import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket06_3
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
private noncomputable def part1632_0 : List Witness := witnesses% "868637340380354624,60401275904,52,45,7,4,64,66,67,68,70;868637340381403200,60401144832,52,45,31,28,65,66,69,70"
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
noncomputable def records1824 : List Witness := []
theorem accepted1824 : records1824.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records1856 : List Witness := []
theorem accepted1856 : records1856.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1888_0 : List Witness := witnesses% "1012195058614683872,60401144832,62,48,41,30,4,3,65,66;1012195058623072480,60401143808,39,19,10,6,5,67,69;1012195075794553056,60401275904,39,19,10,6,5,67,69;1012195075802941664,60401144832,39,19,10,6,5,67,69"
private theorem validpart1888_0 : part1888_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records1888 : List Witness := part1888_0
theorem accepted1888 : records1888.all (validRecord false fullProfiles)=true := by
  exact validpart1888_0
noncomputable def records1920 : List Witness := []
theorem accepted1920 : records1920.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part1952_0 : List Witness := witnesses% "1082837540395984896,60401144832,59,56,22,12,3,65,70;1082837540395984928,60401143808,59,56,22,12,3,65,70;1082841938442496000,60401275904,59,56,22,12,3,65,70;1082841938442496032,60401144832,35,32,20,13,3,64,66,67,68,70"
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
end Quadric.Five.Moves.RPacket06_3
