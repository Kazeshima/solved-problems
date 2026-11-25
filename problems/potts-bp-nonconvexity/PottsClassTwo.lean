import PottsClassZero
import Mathlib.Topology.Algebra.Order.Field

namespace PottsBP
open Finset Set
open Classification
open scoped BigOperators
noncomputable section

theorem Classification.raw_cont {q d : ℕ} (β : ℝ) (p : ℝ → Fin d → Fin q → ℝ)
    (hp : ∀ j i, Continuous (fun s => p s j i)) (i : Fin q) :
    Continuous (fun s => rawWeight β (p s) i) :=
  continuous_finset_prod univ fun j _ => continuous_const.sub (continuous_const.mul (hp j i))

theorem source_convex_two_colors (d : ℕ) (hd : 1 ≤ d) {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    Convex ℝ (admissibleSourceImage 2 d β) := by
  rcases eq_or_lt_of_le h0 with h | hb
  · subst β
    rw [source_image_zero_beta_eq_simplex (by decide) (by simpa using hd)]
    exact convex_stdSimplex _ _
  rw [admissibleSourceImage_eq_generalImage]
  intro x hx y hy a b ha hb' hab
  let z := a • x + b • y
  have hz : simplexN z := (convex_stdSimplex ℝ (Fin 2)) (general_subset_simplex h0 h1 hx)
    (general_subset_simplex h0 h1 hy) ha hb' hab
  obtain ⟨p,hp,_,ep⟩ := hx
  obtain ⟨r,hr,_,er⟩ := hy
  let m (s : ℝ) (j : Fin d) := (1-s) • p j + s • r j
  have hm (s) (hs : s∈Icc (0:ℝ) 1) (j) : simplexN (m s j) :=
    (convex_stdSimplex ℝ (Fin 2)) (hp j) (hr j) (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have hmc (j i) : Continuous (fun s => m s j i) := by simp [m]; fun_prop
  have hZ (s) (hs : s∈Icc (0:ℝ) 1) : 0 < total (rawWeight β (m s)) :=
    total_pos_of_pos (raw_pos (hm s hs) hb h1)
  let F (s : ℝ) := generalBP β (m s) 0
  have hc : ContinuousOn F (Icc 0 1) :=
    (raw_cont β m hmc 0).continuousOn.div
      (continuous_finset_sum univ (fun i _ => raw_cont β m hmc i)).continuousOn
      (fun s hs => (hZ s hs).ne')
  have e0 : F 0=x 0 := by simpa [F,m] using congrFun ep 0
  have e1 : F 1=y 0 := by simpa [F,m] using congrFun er 0
  have hmem : z 0 ∈ uIcc (F 0) (F 1) := by
    rw [e0,e1]
    exact (convex_uIcc (𝕜:=ℝ) _ _) left_mem_uIcc right_mem_uIcc ha hb' hab
  obtain ⟨s,hs,he⟩ := hc.surjOn_uIcc (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) hmem
  have hg : generalBP β (m s) ∈ generalImage 2 d β := ⟨m s,hm s hs,hZ s hs,rfl⟩
  have sg := (general_subset_simplex h0 h1 hg).2
  have sz := hz.2
  simp [Fin.sum_univ_succ] at sg sz
  have he0 : generalBP β (m s) 0=z 0 := he
  have heq : generalBP β (m s)=z := by
    funext i; fin_cases i
    · exact he0
    · change generalBP β (m s) 1=z 1; linarith only [sg,sz,he0]
  rw [heq] at hg
  exact hg

end
end PottsBP
