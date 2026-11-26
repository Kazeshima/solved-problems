import Quadric.Five.Resources.TagBlock00
import Quadric.Five.Resources.TagBlock01
import Quadric.Five.Resources.TagBlock02
import Quadric.Five.Resources.TagBlock03
import Quadric.Five.Resources.TagBlock04
import Quadric.Five.Resources.TagBlock05
import Quadric.Five.Resources.TagBlock06
import Quadric.Five.Resources.TagBlock07
import Quadric.Five.Resources.TagBlock08
import Quadric.Five.Resources.TagBlock09
import Quadric.Five.Resources.TagBlock10
import Quadric.Five.Resources.TagBlock11
import Quadric.Five.Resources.TagBlock12
import Quadric.Five.Resources.TagBlock13
import Quadric.Five.Resources.TagBlock14
import Quadric.Five.Resources.TagBlock15
import Quadric.Five.Resources.TagBlock16
import Quadric.Five.Catalogue
import Quadric.Five.Reduction

namespace Quadric.Five.Tagged.Data
open Small
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
private noncomputable def inside := ((((triples0 ++ triples1) ++ (triples2 ++ (triples3 ++ triples4))) ++ ((triples5 ++ triples6) ++ (triples7 ++ (triples8 ++ triples9)))) ++ (((triples10 ++ triples11) ++ (triples12 ++ (triples13 ++ triples14))) ++ ((triples15 ++ triples16) ++ (triples17 ++ (triples18 ++ triples19)))))
private theorem insideEq : full3=inside := by
  decide +kernel
private theorem insideVR : Valid true inside := (Valid.append (Valid.append (Valid.append (Valid.append valid0 valid1) (Valid.append valid2 (Valid.append valid3 valid4))) (Valid.append (Valid.append valid5 valid6) (Valid.append valid7 (Valid.append valid8 valid9)))) (Valid.append (Valid.append (Valid.append valid10 valid11) (Valid.append valid12 (Valid.append valid13 valid14))) (Valid.append (Valid.append valid15 valid16) (Valid.append valid17 (Valid.append valid18 valid19)))))
private theorem insideTR : Trace inside seen0 seen20 := (Trace.append (Trace.append (Trace.append (Trace.append distinct0 distinct1) (Trace.append distinct2 (Trace.append distinct3 distinct4))) (Trace.append (Trace.append distinct5 distinct6) (Trace.append distinct7 (Trace.append distinct8 distinct9)))) (Trace.append (Trace.append (Trace.append distinct10 distinct11) (Trace.append distinct12 (Trace.append distinct13 distinct14))) (Trace.append (Trace.append distinct15 distinct16) (Trace.append distinct17 (Trace.append distinct18 distinct19)))))
private noncomputable def outside := (((((triples20 ++ (triples21 ++ triples22)) ++ (triples23 ++ (triples24 ++ triples25))) ++ ((triples26 ++ (triples27 ++ triples28)) ++ (triples29 ++ (triples30 ++ triples31)))) ++ (((triples32 ++ (triples33 ++ triples34)) ++ (triples35 ++ (triples36 ++ triples37))) ++ ((triples38 ++ (triples39 ++ triples40)) ++ (triples41 ++ (triples42 ++ triples43))))) ++ ((((triples44 ++ (triples45 ++ triples46)) ++ (triples47 ++ (triples48 ++ triples49))) ++ ((triples50 ++ (triples51 ++ triples52)) ++ (triples53 ++ (triples54 ++ triples55)))) ++ (((triples56 ++ (triples57 ++ triples58)) ++ (triples59 ++ (triples60 ++ triples61))) ++ ((triples62 ++ (triples63 ++ triples64)) ++ (triples65 ++ (triples66 ++ triples67))))))
private theorem outsideEq : outsideLines=outside := by
  unfold outsideLines outsideLine isEdge
  rw [←outside_coordinates]
  decide +kernel
private theorem outsideVR : Valid false outside := (Valid.append (Valid.append (Valid.append (Valid.append (Valid.append valid20 (Valid.append valid21 valid22)) (Valid.append valid23 (Valid.append valid24 valid25))) (Valid.append (Valid.append valid26 (Valid.append valid27 valid28)) (Valid.append valid29 (Valid.append valid30 valid31)))) (Valid.append (Valid.append (Valid.append valid32 (Valid.append valid33 valid34)) (Valid.append valid35 (Valid.append valid36 valid37))) (Valid.append (Valid.append valid38 (Valid.append valid39 valid40)) (Valid.append valid41 (Valid.append valid42 valid43))))) (Valid.append (Valid.append (Valid.append (Valid.append valid44 (Valid.append valid45 valid46)) (Valid.append valid47 (Valid.append valid48 valid49))) (Valid.append (Valid.append valid50 (Valid.append valid51 valid52)) (Valid.append valid53 (Valid.append valid54 valid55)))) (Valid.append (Valid.append (Valid.append valid56 (Valid.append valid57 valid58)) (Valid.append valid59 (Valid.append valid60 valid61))) (Valid.append (Valid.append valid62 (Valid.append valid63 valid64)) (Valid.append valid65 (Valid.append valid66 valid67))))))
private theorem outsideTR : Trace outside seen20 seen68 := (Trace.append (Trace.append (Trace.append (Trace.append (Trace.append distinct20 (Trace.append distinct21 distinct22)) (Trace.append distinct23 (Trace.append distinct24 distinct25))) (Trace.append (Trace.append distinct26 (Trace.append distinct27 distinct28)) (Trace.append distinct29 (Trace.append distinct30 distinct31)))) (Trace.append (Trace.append (Trace.append distinct32 (Trace.append distinct33 distinct34)) (Trace.append distinct35 (Trace.append distinct36 distinct37))) (Trace.append (Trace.append distinct38 (Trace.append distinct39 distinct40)) (Trace.append distinct41 (Trace.append distinct42 distinct43))))) (Trace.append (Trace.append (Trace.append (Trace.append distinct44 (Trace.append distinct45 distinct46)) (Trace.append distinct47 (Trace.append distinct48 distinct49))) (Trace.append (Trace.append distinct50 (Trace.append distinct51 distinct52)) (Trace.append distinct53 (Trace.append distinct54 distinct55)))) (Trace.append (Trace.append (Trace.append distinct56 (Trace.append distinct57 distinct58)) (Trace.append distinct59 (Trace.append distinct60 distinct61))) (Trace.append (Trace.append distinct62 (Trace.append distinct63 distinct64)) (Trace.append distinct65 (Trace.append distinct66 distinct67))))))
theorem valid_inner : Valid true full3 := insideEq.symm ▸ insideVR
theorem distinct_inner : fresh 0 ((full3.flatMap six).map key)=true := by rw [insideEq]; exact insideTR.unique
theorem valid_all : Valid false ellipticLines := by rw [ellipticLines,insideEq,outsideEq]; exact insideVR.weaken.append outsideVR
theorem distinct_all : fresh 0 ((ellipticLines.flatMap six).map key)=true := by
  rw [ellipticLines,insideEq,outsideEq]; exact (insideTR.append outsideTR).unique
theorem exact_if_complete (h : EllipticCompletions) : degree 5=6975 :=
  exact_of_catalogues valid_inner distinct_inner valid_all distinct_all h
end Quadric.Five.Tagged.Data
