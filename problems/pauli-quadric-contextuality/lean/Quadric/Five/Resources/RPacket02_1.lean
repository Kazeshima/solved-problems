import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves.RPacket02_1
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
private noncomputable def part512_0 : List Witness := witnesses% "288235928203359304,567356870022144,60,20,11,5,2,64,66,70;288235928205452360,4449857848384,37,30,12,64,66,67,68,69,70;288235928205456456,4449857852480,37,30,12,64,66,67,68,69,70;288797784551740424,283540423974912,58,45,16,12,10,64,68,69,70;288797775962854408,567356870022144,42,34,20,16,2,65,69;288797784552789000,4458447782976,51,32,25,13,5,2,64,66,67,69,70;288797785626530824,567356870022144,55,31,28,24,11,1,66,68,69,70;288797786700272648,4449857848384,53,40,24,13,3,64,66,67,68;288797784552789064,283540423974912,45,21,12,10,2,64,66,68,69"
private theorem validpart512_0 : part512_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records512 : List Witness := part512_0
theorem accepted512 : records512.all (validRecord false fullProfiles)=true := by
  exact validpart512_0
private noncomputable def part544_0 : List Witness := witnesses% "289361775764235336,4432677983232,62,41,12,4,65,66,69,70;289361810123973704,283540423974912,52,15,5,2,66,69"
private theorem validpart544_0 : part544_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records544 : List Witness := part544_0
theorem accepted544 : records544.all (validRecord false fullProfiles)=true := by
  exact validpart544_0
private noncomputable def part576_0 : List Witness := witnesses% "290482219988833480,4432677983232,45,36,17,9,4,3,65,66,67,69,70;290482219990930632,283540423974912,57,37,18,4,1,64,65,67"
private theorem validpart576_0 : part576_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records576 : List Witness := part576_0
theorem accepted576 : records576.all (validRecord false fullProfiles)=true := by
  exact validpart576_0
private noncomputable def part608_0 : List Witness := witnesses% "291608119895672008,567374049891328,59,55,41,27,64,65,66,67,68;291609219407299784,567356870022144,59,55,41,24,3,66;291608119895676040,4449857852424,52,43,24,14,4,3,65,67,69,70;291608119895676104,4458447787072,37,36,30,12,64,66,67,68,69,70;291608122043159752,4432677983232,56,17,12,7,6,2,67,68,69;291608124190643400,4449857852480,59,30,18,1,65,69,70;291608137075545288,4432677983232,58,38,31,18,1,64,65,67,68,69;291609219407303880,4458447782976,37,36,30,12,64,66,67,68,69,70;291609221554787528,283540423974912,53,37,18,14,8,1,64,65,66,67,68,69,70;291609223702271176,4449857848384,59,30,18,1,65,69,70;291608119895708872,4432677983232,60,44,8,4,3,64,66,69,70;291609219407336648,283540423974912,56,18,14,10,64,65,69;291608119897769160,567356870022144,42,22,18,10,1,64,65,68,69,70;291608119897773256,4458447782976,60,31,24,13,1,64,66,70;291608137077642440,283540423974912,57,48,18,6,5,64,65,66,68,69,70;291608119899870408,4449857852424,62,19,18,10,4,64,68,69;291616915988694216,4450394723336,39,17,16,9,4,68,69;291616915988698312,4449857852424,39,17,16,9,4,68,69;292171069849097352,4450394723336,59,32,29,25,9,65,66,67,70;292171069849097416,567374049891328,55,47,29,26,9,65,66,70;292171074144064712,567356870022144,55,47,29,26,9,65,66,70;292172169360725192,567356870022144,42,25,19,5,4,64,69,70;292171069851194568,567356870022144,56,32,25,14,8,2,64,66,68,69;292171069853291720,4450394723336,62,19,18,10,4,64,68,69"
private theorem validpart608_0 : part608_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records608 : List Witness := part608_0
theorem accepted608 : records608.all (validRecord false fullProfiles)=true := by
  exact validpart608_0
noncomputable def records640 : List Witness := []
theorem accepted640 : records640.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records672 : List Witness := []
theorem accepted672 : records672.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records704 : List Witness := []
theorem accepted704 : records704.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part736_0 : List Witness := witnesses% "364511210462270472,567356870022144,55,49,22,13,7,2,65,67;364511244822008840,4449857852480,53,29,8,5,2,65,68,69;364511245090444296,4449857848384,53,29,8,5,2,65,68,69"
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
private noncomputable def part864_0 : List Witness := witnesses% "435723307971527880,567356870022144,37,27,22,10,1,64,65,68,69,70;435723307971531976,4449857852480,60,31,24,13,1,64,66,70;435723307973629128,4449857848384,60,31,24,13,1,64,66,70;435734323490997448,567356870022144,53,51,20,10,64,66,68,69;435734323490997480,4449857852480,55,25,23,6,5,64,68;435734324564739304,4449857848384,55,25,23,6,5,64,68;436568838855742472,4450394723336,54,28,7,6,4,67,70;436568834564969480,4450394723336,57,28,7,4,67,69;436568838859936776,567374049891328,62,47,29,19,5,64,68,69;436568839128372232,567356870022144,63,46,15,7,6,2,64,65,66,67,68,70;436568838859936840,567356870022144,62,47,29,19,5,64,68,69;436568838859936904,567356870022144,35,31,28,12,4,64"
private theorem validpart864_0 : part864_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records864 : List Witness := part864_0
theorem accepted864 : records864.all (validRecord false fullProfiles)=true := by
  exact validpart864_0
noncomputable def records896 : List Witness := []
theorem accepted896 : records896.all (validRecord false fullProfiles)=true := by
  rfl
noncomputable def records928 : List Witness := []
theorem accepted928 : records928.all (validRecord false fullProfiles)=true := by
  rfl
private noncomputable def part960_0 : List Witness := witnesses% "507500532991022088,4432677983232,47,19,14,12,6,1,64,65,66,68;507500533259457544,283540423974912,51,14,10,2,64,67,69,70"
private theorem validpart960_0 : part960_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records960 : List Witness := part960_0
theorem accepted960 : records960.all (validRecord false fullProfiles)=true := by
  exact validpart960_0
private noncomputable def part992_0 : List Witness := witnesses% "508626432893670408,4449857852424,55,26,18,9,4,68,69,70;508626398538126344,567374049891328,59,49,17,15,3,67,68,70;508626398806561800,567356870022144,35,28,24,15,3,64,65,69;508626428602897416,4449857852424,57,28,7,4,67,69;508626430750381064,4432677983232,62,41,12,4,1,65,66,69,70;508626432897864712,4458447787072,53,29,8,5,2,65,68,69;508626433166300168,4458447782976,53,29,8,5,2,65,68,69;508626432897864776,4449857852480,59,38,23,18,9,1,65,68,69;508626398538126472,567356870022144,59,49,17,15,3,67,68,70;508626430750381192,283540423974912,52,36,15,5,2,66,69;508626432897864840,4458447782976,46,29,13,5,3,2,64,66,67,69,70;508626432897864904,4449857848384,59,38,23,18,9,1,65,68,69;508626398538134536,4450394723336,62,54,4,68,69,70;508626432897872904,4449857852424,62,54,4,68,69,70;508628631921120264,4432677983232,61,45,31,28,7,1,65,66,68,69;508628631921120392,283540423974912,49,38,27,21,10,66,67,68,69,70"
private theorem validpart992_0 : part992_0.all (validRecord false fullProfiles)=true := by decide +kernel
noncomputable def records992 : List Witness := part992_0
theorem accepted992 : records992.all (validRecord false fullProfiles)=true := by
  exact validpart992_0
end Quadric.Five.Moves.RPacket02_1
