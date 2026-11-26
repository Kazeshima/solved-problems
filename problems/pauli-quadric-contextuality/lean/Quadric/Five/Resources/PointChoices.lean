import Quadric.Five.PointWords
import Quadric.Five.Resources.MoveLines

namespace Quadric.Five.Moves.Data
open Small
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option Elab.async false
def pointWords : List (List ℕ) := [[], [41,12], [50,20], [43,12], [32], [33], [34], [35], [41,5], [40,5], [43,5], [42,5], [40], [41], [42], [43], [50,6], [51,6], [48,6], [49,6], [48], [49], [50], [51], [57,5], [56,5], [59,5], [58,5], [56], [57], [58], [59], [4], [5], [6], [7], [], [5,4], [6,4], [7,4], [12], [13], [14], [15], [12,4], [13,4], [14,4], [15,4], [20], [21], [22], [23], [20,4], [21,4], [22,4], [23,4], [28], [29], [30], [31], [28,4], [29,4], [30,4], [31,4]]
def choiceFor (u : ℕ) := equalCatalogues ((hyperLines 36).map (backLine table (pointWords[u]?.getD []))) (hyperLines u)
private theorem choice1 : choiceFor 1=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice2 : choiceFor 2=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice3 : choiceFor 3=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice4 : choiceFor 4=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice5 : choiceFor 5=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice6 : choiceFor 6=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice7 : choiceFor 7=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice8 : choiceFor 8=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice9 : choiceFor 9=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice10 : choiceFor 10=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice11 : choiceFor 11=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice12 : choiceFor 12=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice13 : choiceFor 13=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice14 : choiceFor 14=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice15 : choiceFor 15=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice16 : choiceFor 16=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice17 : choiceFor 17=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice18 : choiceFor 18=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice19 : choiceFor 19=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice20 : choiceFor 20=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice21 : choiceFor 21=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice22 : choiceFor 22=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice23 : choiceFor 23=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice24 : choiceFor 24=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice25 : choiceFor 25=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice26 : choiceFor 26=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice27 : choiceFor 27=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice28 : choiceFor 28=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice29 : choiceFor 29=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice30 : choiceFor 30=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice31 : choiceFor 31=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice32 : choiceFor 32=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice33 : choiceFor 33=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice34 : choiceFor 34=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice35 : choiceFor 35=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice36 : choiceFor 36=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice37 : choiceFor 37=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice38 : choiceFor 38=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice39 : choiceFor 39=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice40 : choiceFor 40=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice41 : choiceFor 41=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice42 : choiceFor 42=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice43 : choiceFor 43=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice44 : choiceFor 44=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice45 : choiceFor 45=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice46 : choiceFor 46=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice47 : choiceFor 47=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice48 : choiceFor 48=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice49 : choiceFor 49=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice50 : choiceFor 50=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice51 : choiceFor 51=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice52 : choiceFor 52=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice53 : choiceFor 53=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice54 : choiceFor 54=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice55 : choiceFor 55=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice56 : choiceFor 56=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice57 : choiceFor 57=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice58 : choiceFor 58=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice59 : choiceFor 59=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice60 : choiceFor 60=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice61 : choiceFor 61=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice62 : choiceFor 62=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem choice63 : choiceFor 63=true := by
  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel
private theorem checked : hyperplanes.all choiceFor=true := by
  rw [show hyperplanes=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] by decide +kernel]
  simp only [List.all_cons,List.all_nil,choice1,choice2,choice3,choice4,choice5,choice6,choice7,choice8,choice9,choice10,choice11,choice12,choice13,choice14,choice15,choice16,choice17,choice18,choice19,choice20,choice21,choice22,choice23,choice24,choice25,choice26,choice27,choice28,choice29,choice30,choice31,choice32,choice33,choice34,choice35,choice36,choice37,choice38,choice39,choice40,choice41,choice42,choice43,choice44,choice45,choice46,choice47,choice48,choice49,choice50,choice51,choice52,choice53,choice54,choice55,choice56,choice57,choice58,choice59,choice60,choice61,choice62,choice63,Bool.and_self]
theorem transport_section (u : ℕ) (hu : u∈hyperplanes) (s : ℕ→Bool) :
    hyperErrors (action table (pointWords[u]?.getD []) s) 36=hyperErrors s u :=
  fix_section _ _ _ _ (List.all_eq_true.mp checked u hu)
end Quadric.Five.Moves.Data
