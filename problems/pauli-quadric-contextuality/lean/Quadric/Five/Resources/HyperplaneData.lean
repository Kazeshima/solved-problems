import Quadric.Five.Hyperplanes
import Quadric.Five.Catalogue
namespace Quadric.Five.Small.HyperplaneData
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option Elab.async false
private noncomputable def triples0 : List Line := signedLines% "1,2,3,0;1,4,5,0;1,6,7,0;1,16,17,0;1,18,19,0;1,20,21,0;1,22,23,0;1,32,33,0;1,34,35,0;1,36,37,0;1,38,39,0;1,48,49,0;1,50,51,0;1,52,53,0;1,54,55,0;2,4,6,0"
private noncomputable def triples1 : List Line := signedLines% "2,5,7,0;2,8,10,0;2,9,11,0;2,12,14,0;2,13,15,0;2,32,34,0;2,33,35,0;2,36,38,0;2,37,39,0;2,40,42,0;2,41,43,0;2,44,46,0;2,45,47,0;3,4,7,0;3,5,6,0;3,24,27,1"
private noncomputable def triples2 : List Line := signedLines% "3,25,26,0;3,28,31,1;3,29,30,0;3,32,35,0;3,33,34,0;3,36,39,0;3,37,38,0;3,56,59,1;3,57,58,0;3,60,63,1;3,61,62,0;4,8,12,0;4,9,13,0;4,10,14,0;4,11,15,0;4,16,20,0"
private noncomputable def triples3 : List Line := signedLines% "4,17,21,0;4,18,22,0;4,19,23,0;4,24,28,0;4,25,29,0;4,26,30,0;4,27,31,0;5,16,21,0;5,17,20,0;5,18,23,0;5,19,22,0;5,40,45,1;5,41,44,0;5,42,47,1;5,43,46,0;5,56,61,1"
private noncomputable def triples4 : List Line := signedLines% "5,57,60,0;5,58,63,1;5,59,62,0;6,8,14,0;6,9,15,0;6,10,12,0;6,11,13,0;6,48,54,1;6,49,55,1;6,50,52,0;6,51,53,0;6,56,62,1;6,57,63,1;6,58,60,0;6,59,61,0;7,24,31,1"
private noncomputable def triples5 : List Line := signedLines% "7,25,30,0;7,26,29,0;7,27,28,1;7,40,47,1;7,41,46,0;7,42,45,1;7,43,44,0;7,48,55,1;7,49,54,1;7,50,53,0;7,51,52,0;8,16,24,0;8,18,26,0;8,20,28,0;8,22,30,0;8,32,40,0"
private noncomputable def triples6 : List Line := signedLines% "8,34,42,0;8,36,44,0;8,38,46,0;8,48,56,0;8,50,58,0;8,52,60,0;8,54,62,0;9,16,25,0;9,18,27,0;9,20,29,0;9,22,31,0;9,32,41,0;9,34,43,0;9,36,45,0;9,38,47,0;9,48,57,0"
private noncomputable def triples7 : List Line := signedLines% "9,50,59,0;9,52,61,0;9,54,63,0;10,17,27,0;10,19,25,1;10,21,31,0;10,23,29,1;10,32,42,0;10,34,40,0;10,36,46,0;10,38,44,0;10,49,59,0;10,51,57,1;10,53,63,0;10,55,61,1;11,17,26,1"
private noncomputable def triples8 : List Line := signedLines% "11,19,24,0;11,21,30,1;11,23,28,0;11,32,43,0;11,34,41,0;11,36,47,0;11,38,45,0;11,49,58,1;11,51,56,0;11,53,62,1;11,55,60,0;12,16,28,0;12,18,30,0;12,20,24,0;12,22,26,0;12,33,45,0"
private noncomputable def triples9 : List Line := signedLines% "12,35,47,0;12,37,41,1;12,39,43,1;12,49,61,0;12,51,63,0;12,53,57,1;12,55,59,1;13,16,29,0;13,18,31,0;13,20,25,0;13,22,27,0;13,33,44,1;13,35,46,1;13,37,40,0;13,39,42,0;13,49,60,1"
private noncomputable def triples10 : List Line := signedLines% "13,51,62,1;13,53,56,0;13,55,58,0;14,17,31,0;14,19,29,1;14,21,27,0;14,23,25,1;14,33,47,0;14,35,45,0;14,37,43,1;14,39,41,1;14,48,62,1;14,50,60,0;14,52,58,0;14,54,56,1;15,17,30,1"
private noncomputable def triples11 : List Line := signedLines% "15,19,28,0;15,21,26,1;15,23,24,0;15,33,46,1;15,35,44,1;15,37,42,0;15,39,40,0;15,48,63,1;15,50,61,0;15,52,59,0;15,54,57,1;16,32,48,0;16,33,49,0;16,36,52,0;16,37,53,0;16,40,56,0"
private noncomputable def triples12 : List Line := signedLines% "16,41,57,0;16,44,60,0;16,45,61,0;17,32,49,0;17,33,48,0;17,36,53,0;17,37,52,0;17,42,59,0;17,43,58,1;17,46,63,0;17,47,62,1;18,32,50,0;18,33,51,0;18,36,54,0;18,37,55,0;18,40,58,0"
private noncomputable def triples13 : List Line := signedLines% "18,41,59,0;18,44,62,0;18,45,63,0;19,32,51,0;19,33,50,0;19,36,55,0;19,37,54,0;19,42,57,1;19,43,56,0;19,46,61,1;19,47,60,0;20,34,54,0;20,35,55,0;20,38,50,1;20,39,51,1;20,42,62,0"
private noncomputable def triples14 : List Line := signedLines% "20,43,63,0;20,46,58,1;20,47,59,1;21,34,55,0;21,35,54,0;21,38,51,1;21,39,50,1;21,40,61,1;21,41,60,0;21,44,57,0;21,45,56,1;22,34,52,1;22,35,53,1;22,38,48,0;22,39,49,0;22,42,60,1"
private noncomputable def triples15 : List Line := signedLines% "22,43,61,1;22,46,56,0;22,47,57,0;23,34,53,1;23,35,52,1;23,38,49,0;23,39,48,0;23,40,63,1;23,41,62,0;23,44,59,0;23,45,58,1;24,32,56,0;24,35,59,1;24,36,60,0;24,39,63,1;24,40,48,0"
private noncomputable def triples16 : List Line := signedLines% "24,43,51,0;24,44,52,0;24,47,55,0;25,32,57,0;25,35,58,0;25,36,61,0;25,39,62,0;25,41,48,0;25,42,51,1;25,45,52,0;25,46,55,1;26,32,58,0;26,35,57,0;26,36,62,0;26,39,61,0;26,40,50,0"
private noncomputable def triples17 : List Line := signedLines% "26,43,49,1;26,44,54,0;26,47,53,1;27,32,59,0;27,35,56,1;27,36,63,0;27,39,60,1;27,41,50,0;27,42,49,0;27,45,54,0;27,46,53,0;28,33,61,0;28,34,62,0;28,37,57,1;28,38,58,1;28,41,53,1"
private noncomputable def triples18 : List Line := signedLines% "28,42,54,0;28,45,49,0;28,46,50,1;29,33,60,1;29,34,63,0;29,37,56,0;29,38,59,1;29,40,53,0;29,43,54,0;29,44,49,1;29,47,50,1;30,33,63,0;30,34,60,1;30,37,59,1;30,38,56,0;30,41,55,1"
private noncomputable def triples19 : List Line := signedLines% "30,42,52,1;30,45,51,0;30,46,48,0;31,33,62,1;31,34,61,1;31,37,58,0;31,38,57,0;31,40,55,0;31,43,52,1;31,44,51,1;31,47,48,0"
private theorem fifteen0 : triples0.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen1 : triples1.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen2 : triples2.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen3 : triples3.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen4 : triples4.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen5 : triples5.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen6 : triples6.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen7 : triples7.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen8 : triples8.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen9 : triples9.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen10 : triples10.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen11 : triples11.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen12 : triples12.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen13 : triples13.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen14 : triples14.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen15 : triples15.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen16 : triples16.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen17 : triples17.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen18 : triples18.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem fifteen19 : triples19.all (fun l=>multiplicity l==15)=true := by decide +kernel
private theorem splitLines : full3=triples0 ++ triples1 ++ triples2 ++ triples3 ++ triples4 ++ triples5 ++ triples6 ++ triples7 ++ triples8 ++ triples9 ++ triples10 ++ triples11 ++ triples12 ++ triples13 ++ triples14 ++ triples15 ++ triples16 ++ triples17 ++ triples18 ++ triples19 := by decide +kernel
theorem fifteen_per_line : ∀l∈full3,multiplicity l=15 := by
  have h : full3.all (fun l=>multiplicity l==15)=true := by
    rw [splitLines]; simp only [List.all_append,fifteen0,fifteen1,fifteen2,fifteen3,fifteen4,fifteen5,fifteen6,fifteen7,fifteen8,fifteen9,fifteen10,fifteen11,fifteen12,fifteen13,fifteen14,fifteen15,fifteen16,fifteen17,fifteen18,fifteen19,Bool.and_self]
  exact fun l hl=>eq_of_beq (List.all_eq_true.mp h l hl)
theorem low_section {s : ℕ→Bool} (low : errors full3 s≤92) :
    ∃u∈hyperplanes,hyperErrors s u≤21 := cheap_hyperplane s low fifteen_per_line
end Quadric.Five.Small.HyperplaneData
