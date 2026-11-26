import Quadric.Five.CensusSemantics
import Quadric.Five.Resources.LevelOne
import Quadric.Five.Hyperplanes

namespace Quadric.Five.Census.LevelOne
open Small
private def fixedSection := full3.filter (inHyperplane 36)
private theorem sameForms :
    ((rawForms system 0 16).map normalized).Perm ((fixedSection.map (lineForm freePoints 0)).map normalized) := by
  decide +kernel

theorem true_section_cost (s : ℕ→Bool) :
    errorCount system (field s 16 9) (field s 0 16)=hyperErrors (extendBits freePoints 0 s) 36 :=
  compare_system system 0 16 fixedSection freePoints 0 sameForms s

/-- The deposited list covers every one of the 25 free hyperplane coordinates, for the
geometric three-qubit line signs and the actual hyperplane of label 36. -/
theorem section_census (s : ℕ→Bool) :
    hyperErrors (extendBits freePoints 0 s) 36 ≤ 21 ↔
      field s 0 16 ∈ survivors[field s 16 9]'(lengths.1.symm ▸ field_lt s 16 9) := by
  rw [←true_section_cost]; exact coverage _ _ (field_lt ..) (field_lt ..)

end Quadric.Five.Census.LevelOne

