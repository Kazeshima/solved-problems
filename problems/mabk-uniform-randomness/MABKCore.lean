import MABKCore.Realization
import MABKCore.Two
import MABKCore.Bipartite

namespace MABK
open Real Finset Set
noncomputable section

def quantumMaximum (n : ℕ) : ℝ := (2:ℝ)^(((n:ℝ)-1)/2)

/-- Eq. (1), including its original prefactor. A subset encodes the parties
choosing input 1. In particular the empty subset is the all-zero input. -/
def mabk {n : ℕ} (p : Finset (Fin n) → Bits n → ℝ) : ℝ :=
  (2:ℝ)^((1-(n:ℝ))/2) * ∑ s ∈ (univ : Finset (Fin n)).powerset,
    cos (((n:ℝ)-1)*π/4-(s.card:ℝ)*π/2)*correlator p s

/-- Eq. (27), with Eq. (24) evaluated at the angle in Eqs. (25) and (26). -/
def publishedMstar (n : ℕ) := quantumMaximum n * eq24 n (publishedAngle n)

theorem score_normalization {n : ℕ} (p : Finset (Fin n) → Bits n → ℝ) :
    mabk p = quantumMaximum n * normalizedScore p := by
  have hc : quantumMaximum n*(2/(2:ℝ)^n) = (2:ℝ)^((1-(n:ℝ))/2) := by
    unfold quantumMaximum
    rw [← Real.rpow_natCast 2 n]
    have hh := Real.rpow_sub (by norm_num : 0<(2:ℝ)) 1 (n:ℝ)
    rw [Real.rpow_one] at hh
    rw [← hh,← Real.rpow_add (by norm_num : 0<(2:ℝ))]
    congr 1; ring
  unfold normalizedScore mabk
  simp only [coefficient,Complex.ofReal_re]
  rw [← hc,mul_assoc,Finset.mul_sum]
  apply congrArg (fun a : ℝ => quantumMaximum n * a)
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem all_even_torus (n : ℕ) (hn : 2 ≤ n) (he : Even n) : TorusDiskClaim n := by
  by_cases h : n=2
  · simpa [h] using torus_disk_two
  · apply torus_disk n he
    obtain ⟨k,hk⟩ := he; omega

theorem published_value (n : ℕ) (he : Even n) :
    publishedMstar n = quantumMaximum n * radius n := by
  rw [publishedMstar,← paper_curve,angle_contact n he]

/-- Upper bound on the vanishing-correlator slice, universe-polymorphic in the
ambient C*-algebra. A normalized mixed state or vector state is contractive. -/
theorem zero_correlator_bound {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {A : Type*} [CStarAlgebra A] (P : ProjectiveStrategy n A) (ω : A →L[ℂ] ℂ)
    (hω : ‖ω‖ ≤ 1) (p : Finset (Fin n) → Bits n → ℝ)
    (born : ∀ s a, ω (outcomeOperator P s a) = (p s a:ℂ))
    (zero : correlator p ∅ = 0) : |mabk p| ≤ publishedMstar n := by
  have hQ : 0 ≤ quantumMaximum n := by unfold quantumMaximum; positivity
  rw [score_normalization,published_value n he,abs_mul,abs_of_nonneg hQ]
  exact mul_le_mul_of_nonneg_left (abs_upper_from_zero P ω hω p born zero (all_even_torus n hn he)) hQ

theorem uniform_upper {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {A : Type*} [CStarAlgebra A] (P : ProjectiveStrategy n A) (ω : A →L[ℂ] ℂ)
    (hω : ‖ω‖ ≤ 1) (p : Finset (Fin n) → Bits n → ℝ)
    (born : ∀ s a, ω (outcomeOperator P s a) = (p s a:ℂ))
    (uniform : ∀ a, p ∅ a = 1/(2:ℝ)^n) : mabk p ≤ publishedMstar n :=
  (le_abs_self _).trans (zero_correlator_bound hn he P ω hω p born (uniform_zero (by omega) p uniform))

def uniformValues (n : ℕ) : Set ℝ := {v | ∃ (e : HilbertBehavior n) (p : Finset (Fin n) → Bits n → ℝ),
  e.Realizes p ∧ (∀ a, p ∅ a = 1/(2:ℝ)^n) ∧ mabk p = v}

theorem tensor_attainment (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : QubitExperiment n, (∀ a, M.prob ∅ a = 1/(2:ℝ)^n) ∧ mabk M.prob = publishedMstar n := by
  have hn' : 0<n := by omega
  refine ⟨ghzExperiment n hn' (publishedAngle n),ghz_uniform n hn' _,?_⟩
  rw [score_normalization,ghz_score,paper_curve,publishedMstar]

/-- Wooltorton–Brown–Colbeck Conjecture 1. Attainment in this same quantum
model is supplied by the explicit, finite-dimensional tensor-product witness. -/
theorem conjecture1 (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    IsGreatest (uniformValues n) (publishedMstar n) := by
  constructor
  · obtain ⟨M,hun,hval⟩ := tensor_attainment n hn
    obtain ⟨e,hr⟩ := tensor_realization M
    exact ⟨e,M.prob,hr,hun,hval⟩
  · rintro v ⟨e,p,hborn,hun,rfl⟩
    exact uniform_upper hn he e.P (vectorState e.ψ) (vectorState_contractive e.ψ e.norm_one) p hborn hun

end
end MABK
