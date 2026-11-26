import Quadric.Five.FortyTwo
import Quadric.Five.Resources.TaggedLines

namespace Quadric.Five
open Tagged Small

/-- Each low-error three-qubit restriction lifts to a certified elliptic profile
with no more violated elliptic lines. -/
def ProfileCoverage : Prop := ∀ s : ℕ → Bool, errors full3 s ≤ 92 →
  ∃ t : ℕ → Bool, carrier t ∈ Certificates.sigmas ∧ errors ellipticLines t ≤ errors ellipticLines s

theorem listed_profile_bound (s : ℕ→Bool) (listed : carrier s∈Certificates.sigmas) :
    315≤errors ellipticLines s := by
  rw [partition_errors]
  exact Certificates.all_42_certificates listed (fun i=>s (64+i))

theorem degree_five_of_profile_coverage (h : ProfileCoverage) : degree 5=6975 := by
  apply Tagged.Data.exact_if_complete
  intro s hs
  obtain ⟨t,ht,hcost⟩ := h s hs
  exact (listed_profile_bound t ht).trans hcost

end Quadric.Five
