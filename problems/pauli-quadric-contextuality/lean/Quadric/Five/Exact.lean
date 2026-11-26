import Quadric.Five.CloseCensus
import Quadric.Five.ProfileReduction
import Quadric.Five.Resources.AllCases
import Quadric.Five.Resources.AllHyperplanes
import Quadric.Five.Resources.AllMoves
import Quadric.Five.Resources.GaugeChecks

namespace Quadric.Five
open Tagged Small
theorem profile_masks_match : Moves.Data.fullProfiles=Certificates.sigmas := by decide +kernel

theorem census_classification (s : ℕ→Bool) (hs : errors full3 s≤92) :
    ∃t : ℕ→Bool, carrier t∈Certificates.sigmas ∧ errors ellipticLines t=errors ellipticLines s ∧
      Moves.Reach Moves.Data.table s t := by
  rw [←profile_masks_match]
  exact Moves.classification_to_bounds Moves.Data.all_good Moves.Data.all_gauges
    Moves.Data.hyperplane_census Moves.Data.complete_cases s hs

private theorem trim_word (t : List Moves.Move) (w : List ℕ) (x : ℕ) :
    Moves.walk t (w.filter (·<t.length)) x=Moves.walk t w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i is ih =>
    by_cases valid : i<t.length
    · simp only [List.filter_cons,decide_eq_true_eq,valid,if_true,Moves.walk,ih]
    · have missing : t[i]?=none := List.getElem?_eq_none (Nat.le_of_not_lt valid)
      simp [List.filter_cons,valid,Moves.walk,missing,ih]

/-- A signed word takes every low-error section signature to a submitted certificate. -/
theorem all_low_signatures_in_orbits (s : ℕ→Bool) (hs : errors full3 s≤92) :
    ∃ w : List ℕ, (∀i∈w,i<Moves.Data.table.length) ∧
      Moves.walk Moves.Data.table w (carrier s)∈Certificates.sigmas := by
  obtain ⟨t,good,_,w,rfl⟩:=census_classification s hs
  refine ⟨w.filter (·<Moves.Data.table.length),fun i hi=>of_decide_eq_true (List.mem_filter.mp hi).2,?_⟩
  rw [trim_word]; exact (Moves.travel _ Moves.Data.all_good w s).1 ▸ good

theorem hyperplane_profile_count : Moves.Data.hProfiles.length=18 ∧ Moves.Data.hProfiles.Nodup := by decide +kernel

theorem every_low_restriction : ProfileCoverage := by
  intro s hs
  obtain ⟨t,target,cost,_⟩:=census_classification s hs
  exact ⟨t,target,cost.le⟩

/-- Exact contextuality degree for the signed Pauli lines of the five-qubit hyperbolic quadric. -/
theorem degree_five : degree 5=6975 := degree_five_of_profile_coverage every_low_restriction

end Quadric.Five

