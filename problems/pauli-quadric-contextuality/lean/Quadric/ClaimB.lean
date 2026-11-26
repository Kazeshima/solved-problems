import Quadric.Classification
import Quadric.PolarIso

namespace Quadric.Four
open Matrix Finset
attribute [local irreducible] points lines pairs bad violations level height

/-- Restriction of an arbitrary sign function from the all-rank API to its measured points. -/
def restrictSigns (s : Assignment 4) : Signing := fun p => if s p.val then 1 else 0

theorem value_restrict (s : Assignment 4) {p : Lab} (hp : p∈points 4) :
    value (assign (restrictSigns s) p)=value (s p) := by
  rw [sign_value]; simp only [spin,dif_pos hp,restrictSigns]
  cases s p <;> norm_num [value,chi]

theorem violations_restrict (s : Assignment 4) : violations (restrictSigns s) = bad s := by
  unfold violations
  ext l
  by_cases hl : l∈lines 4
  · unfold lines at hl
    obtain ⟨⟨p,r⟩,hh,rfl⟩ := mem_image.mp hl
    obtain ⟨hp,hr,ht⟩ := mem_pairs.mp hh
    rw [bad_triple_iff _ hh,bad_triple_iff _ hh,score_eval _ hh,score_eval _ hh,
      value_restrict s hp,value_restrict s hr,value_restrict s ht]
  · simp [bad,hl]

/-- One real orthogonal Pauli normalizer simultaneously transports the signed assignment,
its signed Pauli sum, and its entire violated-line configuration. -/
theorem every_optimal_assignment (s : Assignment 4) (hs : (bad s).card=degree 4) :
    ∃ C : Clifford 4,
      (∀ p ∈ points 4, value (s (C.perm p)) = chi (C.phase p)*value (mixed p)) ∧
      operator s = C.U * operator mixed * C.Uᵀ ∧
      bad s = (bad mixed).image (lineMap C) := by
  let t : Opt := ⟨restrictSigns s,by rw [violations_restrict]; exact hs⟩
  obtain ⟨C,hC⟩ := every_optimum_in_orbit t
  change push C canonical=restrictSigns s at hC
  refine ⟨C,?_,?_,?_⟩
  · intro p hp
    rw [←value_restrict s ((C.map_point p).mpr hp),←hC,sign_value,spin_push C canonical hp,
      chi_add,mul_comm (chi (spin canonical p))]
    rw [←sign_value]; rw [canonical_value hp]
  · have hm : matrixOf (restrictSigns s) = operator s :=
      operator_eq_of_signs (fun _ hp => value_restrict s hp)
    rw [←hm,←hC,matrix_push,matrix_canonical,←witness_operator]; rfl
  · rw [←violations_restrict s,←hC,←map_bad,violations_canonical]

theorem optimal_iff_canonical_orbit (s : Signing) :
    (violations s).card = degree 4 ↔ InCanonicalOrbit s := by
  constructor
  · intro hs; exact every_optimum_in_orbit ⟨s,hs⟩
  · rintro ⟨C,rfl⟩; exact (optMove C canonicalOpt).property

/-- A point bijection and a line bijection preserving and reflecting incidence. -/
theorem every_optimum_DW (s : Opt) : Nonempty (DWIso s.val) := by
  obtain ⟨C,hC⟩ := every_optimum_in_orbit s
  rw [←hC]
  exact ⟨transportIso C canonicalIso⟩

theorem classification :
    (∀ s : Opt, InCanonicalOrbit s.val ∧ Nonempty (DWIso s.val)) ∧
    Fintype.card Opt=61440 ∧ configurations.card=240 :=
  ⟨fun s => ⟨every_optimum_in_orbit s,every_optimum_DW s⟩,
    optimal_assignments_count,optimal_configurations_count⟩

end Quadric.Four
