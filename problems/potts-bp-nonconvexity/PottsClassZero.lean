import PottsClassBasic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace PottsBP
open Finset Set
open Classification
open scoped BigOperators
noncomputable section

private theorem zero_star {n : ℕ} {x : Fin (n+1) → ℝ} (hx : simplexN x) :
    x ∈ generalImage (n+1) n 0 := by
  classical
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image univ x Finset.univ_nonempty
  have hmax' (i : Fin (n+1)) : x i ≤ x a := hmax i (mem_univ i)
  have hxa : 0 < x a := by
    by_contra! hn
    have hzero (i) : x i = 0 := le_antisymm ((hmax' i).trans hn) (hx.1 i)
    have := hx.2
    simp [hzero] at this
  let f := a.succAboveEmb
  let y (j : Fin n) := x (f j) / x a
  have hy0 (j) : 0 ≤ y j := div_nonneg (hx.1 _) hxa.le
  have hy1 (j) : y j ≤ 1 := (div_le_one hxa).2 (hmax' _)
  let H (s : ℝ) := (∏ j, (1-s*y j))-s
  have hcont : Continuous H := by dsimp [H]; fun_prop
  have hleft : H 0 = 1 := by simp [H]
  have hright : H 1 ≤ 0 := by
    have hh : ∏ j, (1-y j) ≤ 1 := Finset.prod_le_one (fun j _ => sub_nonneg.mpr (hy1 j))
      (fun j _ => sub_le_self _ (hy0 j))
    simpa [H] using (sub_nonpos.mpr hh)
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont.continuousOn
    (show (0:ℝ) ∈ Icc (H 1) (H 0) from ⟨hright,hleft.symm ▸ zero_le_one⟩)
  have hsp : 0 < s := lt_of_le_of_ne hs.1 (fun h => by subst s; linarith)
  let z (j : Fin n) := s*y j
  have hz0 (j) : 0 ≤ z j := mul_nonneg hs.1 (hy0 j)
  have hz1 (j) : z j ≤ 1 := mul_le_one₀ hs.2 (hy0 j) (hy1 j)
  let pin (k : Fin (n+1)) (i : Fin (n+1)) : ℝ := if k=i then 1 else 0
  let p (j : Fin n) := z j • pin a + (1-z j) • pin (f j)
  have hp (j) : simplexN (p j) :=
    (convex_stdSimplex ℝ (Fin (n+1))) (singleton_pin a) (singleton_pin (f j))
      (hz0 j) (sub_nonneg.mpr (hz1 j)) (by ring)
  have hfa (j : Fin n) : f j ≠ a := Fin.succAbove_ne _ _
  have ga : rawWeight 0 p a = s := by
    simp only [rawWeight,p,pin,Pi.add_apply,Pi.smul_apply,smul_eq_mul,if_pos rfl,
      if_true,if_neg (hfa _),mul_one,mul_zero,add_zero,sub_zero,one_mul]
    exact sub_eq_zero.mp he
  have gf (k : Fin n) : rawWeight 0 p (f k) = z k := by
    calc
      _ = ∏ j, (if j=k then z k else 1) := by
        apply prod_congr rfl; intro j _
        by_cases hj : j=k
        · subst j; simp [p,pin,(hfa k).symm]
        · simp [p,pin,(hfa k).symm,show f j ≠ f k from fun h => hj (f.injective h),hj]
      _ = _ := by simp
  let c := s / x a
  have hc : 0 < c := div_pos hsp hxa
  have gw (i) : rawWeight 0 p i = c*x i := by
    by_cases hi : i=a
    · subst i; rw [ga]; dsimp [c]; field_simp
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
      change f j = i at hj
      rw [← hj,gf]; dsimp [z,y,c]; ring
  have hZ : (∑ i,rawWeight 0 p i) = c := by simp only [gw, ← mul_sum,hx.2,mul_one]
  refine ⟨p,hp,hZ.symm ▸ hc,?_⟩
  funext i
  change rawWeight 0 p i / (∑ k,rawWeight 0 p k) = x i
  rw [hZ,gw]
  exact (div_eq_iff hc.ne').2 (mul_comm _ _)

theorem source_image_zero_beta_eq_simplex {q d : ℕ} (hq : 2 ≤ q) (hd : q-1 ≤ d) :
    admissibleSourceImage q d 0 = stdSimplex ℝ (Fin q) := by
  rw [admissibleSourceImage_eq_generalImage]
  apply Set.Subset.antisymm (general_subset_simplex (by norm_num) (by norm_num))
  intro x hx
  cases q with
  | zero => omega
  | succ n =>
    exact general_mono_degree hq (by norm_num) (by simpa using hd) (zero_star hx)

end
end PottsBP
