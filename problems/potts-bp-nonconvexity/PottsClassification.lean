import PottsClassHot
import PottsClassThree

namespace PottsBP
open Finset Set Classification
open scoped BigOperators
noncomputable section

theorem admissibleSourceImage_eq_sourceImage_diff_zero {q d : ℕ} {β : ℝ} (h0 : 0≤β) (h1 : β≤1) :
    admissibleSourceImage q d β = sourceImage q d β \ {0} := by
  rw [admissibleSourceImage_eq_generalImage]
  ext x
  constructor
  · intro hx
    have hs := (general_subset_simplex h0 h1 hx).2
    obtain ⟨p,hp,hZ,hx⟩ := hx
    refine ⟨⟨p,hp,(sourceBP_eq_generalBP β p hp).trans hx⟩,?_⟩
    rintro (rfl : x=0)
    simp at hs
  · rintro ⟨⟨p,hp,hx⟩,hn⟩
    have eq := (sourceBP_eq_generalBP β p hp).symm.trans hx
    refine ⟨p,hp,?_,eq⟩
    have hnon := sum_nonneg (s:=univ) (fun i _ => raw_nonneg hp h0 h1 i)
    apply lt_of_le_of_ne hnon
    intro hz
    apply hn
    change x=0
    rw [← eq]
    funext i
    simp [generalBP,← hz]

theorem legacy_zero_image {q d : ℕ} (hq : 2≤q) (hd : q≤d) :
    sourceImage q d 0 = insert 0 (stdSimplex ℝ (Fin q)) := by
  classical
  have hg := admissibleSourceImage_eq_sourceImage_diff_zero (q:=q) (d:=d)
    (by norm_num : 0≤(0:ℝ)) (by norm_num)
  rw [source_image_zero_beta_eq_simplex hq (by omega)] at hg
  have hzero : (0 : Fin q → ℝ) ∈ sourceImage q d 0 := by
    letI : NeZero q := ⟨by omega⟩
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
    have rz := realizes_pins (0:ℝ) (Function.Embedding.refl (Fin q))
    have rz' : Realizes q q 0 (fun _ => 0) := by simpa using rz
    have zz := add_pins rz' 0 k
    obtain ⟨p,hp,hp0⟩ := zz
    refine ⟨p,hp,?_⟩
    rw [sourceBP_eq_generalBP _ _ hp]
    funext i; simp [generalBP,hp0]
  ext x
  by_cases hx : x=0
  · subst x; simp [hzero]
  · have he := Set.ext_iff.mp hg x
    simpa [hx] using he.symm

theorem source_nonconvex_iff {q d : ℕ} (hq : 2≤q) (hd : 1≤d) {β : ℝ}
    (hb : 0≤β) (h1 : β≤1) :
    ¬ Convex ℝ (admissibleSourceImage q d β) ↔
      4≤q ∧ 2≤d ∧ ((0<β ∧ β<1) ∨ (β=0 ∧ d≤q-2)) := by
  constructor
  · intro hn
    have hd2 : 2≤d := by
      by_contra! hs
      have eq : d=1 := by omega
      subst d
      exact hn (source_convex_one_neighbor hq hb)
    have hq4 : 4≤q := by
      by_contra! hs
      have eq : q=2 ∨ q=3 := by omega
      rcases eq with rfl|rfl
      · exact hn (source_convex_two_colors _ hd hb h1)
      · exact hn (source_convex_three_colors hd hb h1)
    refine ⟨hq4,hd2,?_⟩
    rcases eq_or_lt_of_le hb with h|h
    · subst β
      right; refine ⟨rfl,?_⟩
      by_contra! bad
      have full := source_image_zero_beta_eq_simplex (d:=d) hq (by omega)
      exact hn (full.symm ▸ convex_stdSimplex _ _)
    · left; refine ⟨h,?_⟩
      exact lt_of_le_of_ne h1 (fun eq => by subst β; exact hn (source_convex_beta_one _ _))
  · rintro ⟨hq4,hd2,h|⟨rfl,hdq⟩⟩
    · exact source_nonconvex_positive_beta hq4 hd2 h.1 h.2
    · rw [admissibleSourceImage_eq_generalImage]
      exact nonconvex_general hd2 (by omega) (by norm_num) (by norm_num)

theorem source_nonconvex_iff_on_defined_outputs {q d : ℕ} (hq : 2≤q) (hd : 1≤d)
    {β : ℝ} (hb : 0≤β) (h1 : β≤1) :
    ¬Convex ℝ (sourceImage q d β \ {0}) ↔
      4≤q ∧ 2≤d ∧ ((0<β ∧ β<1) ∨ (β=0 ∧ d≤q-2)) := by
  rw [← admissibleSourceImage_eq_sourceImage_diff_zero hb h1]
  exact source_nonconvex_iff hq hd hb h1

theorem sourceImage_eq_admissible_positive {q d : ℕ} (hq : 0<q) {β : ℝ} (hb : 0<β) (h1 : β≤1) :
    sourceImage q d β = admissibleSourceImage q d β := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact legacy_eq_of_pos (fun _ hp => total_pos_of_pos (raw_pos hp hb h1))

/-- Signature-level check with the joint finite expectation and every domain quantifier displayed. -/
theorem paper_classification {q d : ℕ} (hq : 2≤q) (hd : 1≤d) {β : ℝ} (hb : 0≤β) (h1 : β≤1) :
    let G (p : Fin d → Fin q → ℝ) (i : Fin q) :=
      ∑ τ : Fin d → Fin q, (∏ j,p j (τ j)) * ∏ j,(if i=τ j then β else 1)
    ¬Convex ℝ {x : Fin q → ℝ | ∃ p : Fin d → Fin q → ℝ,
      (∀ j, (∀ i, 0≤p j i) ∧ (∑ i,p j i)=1) ∧ (0<∑ i,G p i) ∧
      (fun i => G p i/(∑ k,G p k))=x} ↔
      4≤q ∧ 2≤d ∧ ((0<β ∧ β<1) ∨ (β=0 ∧ d≤q-2)) :=
  source_nonconvex_iff hq hd hb h1

end
end PottsBP
