import PottsClassEdges
import PottsClassFiber

namespace PottsBP
open Finset Set
open scoped BigOperators
noncomputable section
namespace Classification

private lemma edge_chart {β : ℝ} (hb : 0<β) {a b c : Fin 3} (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    {m n : ℕ} {s : ℝ} {g : Fin 3 → ℝ} (hg : g=edgeWeight β a b m n s) :
    (1+β)*(g c / g 1) = (g a/g 1)/β^m+(g b/g 1)/β^n := by
  have h : (1+β)*g c = g a/β^m+g b/β^n := by rw [hg]; exact edge_equality hb hab hac hbc m n s
  calc
    _ = ((1+β)*g c)/g 1 := by ring
    _ = _ := by rw [h]; ring

theorem three_fill {d : ℕ} (hd : 1≤d) {β : ℝ} (hb : 0<β) (h1 : β<1)
    {x : Fin 3 → ℝ} (hx : simplexN x) (pos : ∀ i,0<x i) (bound : Bounds d β x) :
    x∈generalImage 3 d β := by
  let R:= x 0/x 1
  let W:= x 2/x 1
  let y (i : Fin 3) := (x 1)⁻¹*x i
  have hy : Bounds d β y := bounds_scale (inv_pos.mpr (pos 1)).le bound
  have y0 : y 0=R := by dsimp [y,R]; ring
  have y1 : y 1=1 := inv_mul_cancel₀ (pos 1).ne'
  have y2 : y 2=W := by dsimp [y,W]; ring
  have hR : 0<R := div_pos (pos 0) (pos 1)
  have rlo := hy.1 0 1
  have rhi := hy.1 1 0
  rw [y0,y1,mul_one] at rlo
  rw [y0,y1,mul_comm] at rhi
  obtain ⟨m,n,s,r,hm,hr,ew,er⟩ := edge_cross hd β R 0 1
    (by simpa [pinFactor] using rlo) (by simpa [pinFactor] using rhi)
  have rp := raw_pos hr hb h1.le
  have eqr := edge_chart hb (by decide : (0:Fin 3)≠1) (by decide : (0:Fin 3)≠2) (by decide : (1:Fin 3)≠2) ew
  rw [(div_eq_iff (rp 1).ne').2 er,div_self (rp 1).ne'] at eqr
  have boundUp := hy.2 0 1 2 m n (by decide) hm
  rw [y0,y1,y2] at boundUp
  have hh : W ≤ rawWeight β r 2/rawWeight β r 1 :=
    (mul_le_mul_left (show 0<1+β by linarith)).mp (boundUp.trans_eq eqr.symm)
  have lx : ∃ p : Fin d → Fin 3 → ℝ, (∀ j,simplexN (p j)) ∧ rawWeight β p 0=R*rawWeight β p 1 ∧
      rawWeight β p 2/rawWeight β p 1 ≤ W := by
    by_cases high : 1≤R
    · obtain ⟨m,n,s,p,hm,hp,ew,er⟩ := edge_cross hd β R 2 1
        (by simpa [pinFactor] using high) (by simpa [pinFactor] using rhi)
      refine ⟨p,hp,er,?_⟩
      have pp := raw_pos hp hb h1.le
      have equ := edge_chart hb (by decide : (2:Fin 3)≠1) (by decide : (2:Fin 3)≠0) (by decide : (1:Fin 3)≠0) ew
      rw [(div_eq_iff (pp 1).ne').2 er,div_self (pp 1).ne'] at equ
      have bnd := hy.2 2 1 0 m n (by decide) hm
      rw [y0,y1,y2,equ] at bnd
      exact (div_le_div_iff_of_pos_right (pow_pos hb m)).mp (le_of_add_le_add_right bnd)
    · obtain ⟨m,n,s,p,hm,hp,ew,er⟩ := edge_cross hd β R 0 2
        (by simpa [pinFactor] using rlo) (by simpa [pinFactor] using le_of_not_ge high)
      refine ⟨p,hp,er,?_⟩
      have pp := raw_pos hp hb h1.le
      have equ := edge_chart hb (by decide : (0:Fin 3)≠2) (by decide : (0:Fin 3)≠1) (by decide : (2:Fin 3)≠1) ew
      rw [(div_eq_iff (pp 1).ne').2 er,div_self (pp 1).ne'] at equ
      have bnd := hy.2 0 2 1 m n (by decide) hm
      rw [y0,y1,y2,equ] at bnd
      exact (div_le_div_iff_of_pos_right (pow_pos hb n)).mp (le_of_add_le_add_left bnd)
  obtain ⟨p,hp,ep,hl⟩ := lx
  obtain ⟨z,hz,e0,e2⟩ := height_intermediate hb h1 hR p r hp hr ep er hl hh
  let c := rawWeight β z 1 / x 1
  have cp : 0<c := div_pos (raw_pos hz hb h1.le _) (pos 1)
  have each (i) : rawWeight β z i=c*x i := by
    fin_cases i
    · change rawWeight β z 0=c*x 0
      rw [e0]; dsimp [c,R]; ring
    · change rawWeight β z 1=c*x 1
      dsimp [c]; field_simp [(pos 1).ne']
    · change rawWeight β z 2=c*x 2
      rw [e2]; dsimp [c,W]; ring
  have hZ : (∑ i,rawWeight β z i)=c := by simp only [each,← mul_sum,hx.2,mul_one]
  refine ⟨z,hz,hZ.symm ▸ cp,?_⟩
  funext i
  change rawWeight β z i / (∑ k,rawWeight β z k) = x i
  rw [hZ,each]; exact (div_eq_iff cp.ne').2 (mul_comm _ _)

end Classification
open Classification

theorem source_convex_three_colors {d : ℕ} (hd : 1≤d) {β : ℝ} (h0 : 0≤β) (h1 : β≤1) :
    Convex ℝ (admissibleSourceImage 3 d β) := by
  rcases eq_or_lt_of_le h0 with h|hb
  · subst β
    by_cases h : d=1
    · subst d; exact source_convex_one_neighbor (by decide) (by norm_num)
    · rw [source_image_zero_beta_eq_simplex (by decide) (by omega)]
      exact convex_stdSimplex _ _
  rcases eq_or_lt_of_le h1 with h|h1
  · subst β; exact source_convex_beta_one _ _
  rw [admissibleSourceImage_eq_generalImage]
  intro x hx y hy a b ha hb' hab
  have positive {v : Fin 3 → ℝ} (hv : v∈generalImage 3 d β) (i) : 0<v i := by
    obtain ⟨p,hp,hZ,rfl⟩ := hv; exact div_pos (raw_pos hp hb h1.le i) hZ
  apply three_fill hd hb h1
  · exact (convex_stdSimplex ℝ (Fin 3)) (general_subset_simplex hb.le h1.le hx)
      (general_subset_simplex hb.le h1.le hy) ha hb' hab
  · intro i
    change 0<a*x i+b*y i
    rcases eq_or_lt_of_le ha with h|h
    · subst a; simp_all [positive hy i]
    · exact add_pos_of_pos_of_nonneg (mul_pos h (positive hx i)) (mul_nonneg hb' (positive hy i).le)
  · exact bounds_add (bounds_scale ha (bounds_of_mem hb h1 hx)) (bounds_scale hb' (bounds_of_mem hb h1 hy))

end
end PottsBP
