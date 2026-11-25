import PottsClassTwo
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PottsBP.Classification
open Finset Set
open scoped BigOperators
noncomputable section

private def gm (s a b : ℝ) := Real.exp ((1-s)*Real.log a+s*Real.log b)
private lemma gm_zero {a b : ℝ} (ha : 0<a) : gm 0 a b = a := by simp [gm,Real.exp_log ha]
private lemma gm_one {a b : ℝ} (hb : 0<b) : gm 1 a b = b := by simp [gm,Real.exp_log hb]

private lemma gm_bounds {s β a b : ℝ} (hs : s∈Icc (0:ℝ) 1) (hb : 0<β)
    (ha : a∈Icc β 1) (hc : b∈Icc β 1) : gm s a b∈Icc β 1 := by
  have hsn := sub_nonneg.mpr hs.2
  have low := add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log hb ha.1) hsn)
    (mul_le_mul_of_nonneg_left (Real.log_le_log hb hc.1) hs.1)
  have hi := add_le_add (mul_le_mul_of_nonneg_left (Real.log_nonpos (hb.le.trans ha.1) ha.2) hsn)
    (mul_le_mul_of_nonneg_left (Real.log_nonpos (hb.le.trans hc.1) hc.2) hs.1)
  constructor
  · calc
      β = Real.exp (Real.log β) := (Real.exp_log hb).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [low] : Real.log β ≤ (1-s)*Real.log a+s*Real.log b)
  · exact Real.exp_le_one_iff.mpr (by linarith only [hi])

private def stretch (β u v : ℝ) := max 1 ((1+β)/(u+v))

private def project (β u v : ℝ) : Fin 3 → ℝ :=
  ![(1-stretch β u v*u)/(1-β),(1-stretch β u v*v)/(1-β),(stretch β u v*(u+v)-(1+β))/(1-β)]

private lemma project_simplex {β u v : ℝ} (hb : 0<β) (h1 : β<1)
    (hu : u∈Icc β 1) (hv : v∈Icc β 1) : simplexN (project β u v) := by
  have ht := sub_pos.mpr h1
  have huv : 0<u+v := add_pos (hb.trans_le hu.1) (hb.trans_le hv.1)
  have a : stretch β u v*u ≤ 1 := by
    rcases le_total ((1+β)/(u+v)) 1 with hh|hh
    · simpa [stretch,max_eq_left hh] using hu.2
    · rw [stretch,max_eq_right hh,div_mul_eq_mul_div,div_le_iff₀ huv]
      nlinarith only [mul_le_mul_of_nonneg_left hu.2 hb.le,hv.1]
  have b : stretch β u v*v ≤ 1 := by
    rcases le_total ((1+β)/(u+v)) 1 with hh|hh
    · simpa [stretch,max_eq_left hh] using hv.2
    · rw [stretch,max_eq_right hh,div_mul_eq_mul_div,div_le_iff₀ huv]
      nlinarith only [mul_le_mul_of_nonneg_left hv.2 hb.le,hu.1]
  have c : 1+β ≤ stretch β u v*(u+v) := (div_le_iff₀ huv).mp (le_max_right _ _)
  constructor
  · intro i
    fin_cases i
    · exact div_nonneg (sub_nonneg.mpr a) ht.le
    · exact div_nonneg (sub_nonneg.mpr b) ht.le
    · exact div_nonneg (sub_nonneg.mpr c) ht.le
  · simp [project,Fin.sum_univ_succ]
    field_simp
    ring

private lemma project_f0 {β u v : ℝ} (hb : β<1) :
    1-(1-β)*project β u v 0=stretch β u v*u := by
  change 1-(1-β)*((1-stretch β u v*u)/(1-β))=_
  field_simp [sub_ne_zero.mpr hb.ne']
private lemma project_f1 {β u v : ℝ} (hb : β<1) :
    1-(1-β)*project β u v 1=stretch β u v*v := by
  change 1-(1-β)*((1-stretch β u v*v)/(1-β))=_
  field_simp [sub_ne_zero.mpr hb.ne']

private def fac (β : ℝ) (p : Fin 3 → ℝ) (i : Fin 3) := 1-(1-β)*p i

private lemma fac_mem {β : ℝ} (h1 : β≤1) {p : Fin 3 → ℝ} (hp : simplexN p) (i) :
    fac β p i∈Icc β 1 := by
  refine ⟨?_,sub_le_self _ (mul_nonneg (sub_nonneg.mpr h1) (hp.1 i))⟩
  dsimp [fac]; nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (simplexN_le_one hp i))]

private lemma project_restore {β : ℝ} (hb : 0<β) (h1 : β<1) {p : Fin 3 → ℝ} (hp : simplexN p) :
    project β (fac β p 0) (fac β p 1)=p := by
  have ht := sub_pos.mpr h1
  have sp : p 0+p 1+p 2=1 := by simpa [Fin.sum_univ_succ,add_assoc] using hp.2
  have hsum : 0<fac β p 0+fac β p 1 := add_pos (hb.trans_le (fac_mem h1.le hp 0).1)
    (hb.trans_le (fac_mem h1.le hp 1).1)
  have ss : stretch β (fac β p 0) (fac β p 1)=1 := by
    apply max_eq_left
    apply (div_le_one hsum).2
    dsimp [fac]
    nlinarith only [mul_nonneg ht.le (hp.1 2),congrArg (fun z : ℝ => (1-β)*z) sp]
  funext i
  fin_cases i
  · change (1-stretch _ _ _*fac β p 0)/(1-β)=p 0
    rw [ss]; apply (div_eq_iff ht.ne').2; dsimp [fac]; ring
  · change (1-stretch _ _ _*fac β p 1)/(1-β)=p 1
    rw [ss]; apply (div_eq_iff ht.ne').2; dsimp [fac]; ring
  · change (stretch _ _ _*(fac β p 0+fac β p 1)-(1+β))/(1-β)=p 2
    rw [ss]; apply (div_eq_iff ht.ne').2; dsimp [fac]
    linear_combination -(1-β)*sp

private lemma prod_gm {d : ℕ} (s : ℝ) (a b : Fin d → ℝ) (ha : ∀ j,0<a j) (hb : ∀ j,0<b j) :
    (∏ j,gm s (a j) (b j)) = gm s (∏ j,a j) (∏ j,b j) := by
  simp only [gm,← Real.exp_sum,sum_add_distrib,← mul_sum,
    Real.log_prod univ a (fun j _ => (ha j).ne'),Real.log_prod univ b (fun j _ => (hb j).ne')]

private lemma gm_scale (s : ℝ) {R a b : ℝ} (hr : 0<R) (ha : 0<a) (hb : 0<b) :
    gm s (R*a) (R*b)=R*gm s a b := by
  unfold gm
  rw [Real.log_mul hr.ne' ha.ne',Real.log_mul hr.ne' hb.ne']
  rw [show (1-s)*(Real.log R+Real.log a)+s*(Real.log R+Real.log b) =
    Real.log R+((1-s)*Real.log a+s*Real.log b) by ring,Real.exp_add,Real.exp_log hr]

/-- A projective ratio fibre contains an interpolant at every intermediate height. -/
theorem height_intermediate {d : ℕ} {β R W : ℝ} (hb : 0<β) (h1 : β<1) (hR : 0<R)
    (p r : Fin d → Fin 3 → ℝ) (hp : ∀ j,simplexN (p j)) (hr : ∀ j,simplexN (r j))
    (ep : rawWeight β p 0=R*rawWeight β p 1) (er : rawWeight β r 0=R*rawWeight β r 1)
    (lo : rawWeight β p 2/rawWeight β p 1≤W) (hi : W≤rawWeight β r 2/rawWeight β r 1) :
    ∃ z : Fin d → Fin 3 → ℝ, (∀ j,simplexN (z j)) ∧ rawWeight β z 0=R*rawWeight β z 1 ∧
      rawWeight β z 2=W*rawWeight β z 1 := by
  let A (s : ℝ) (j : Fin d) (i : Fin 3) := gm s (fac β (p j) i) (fac β (r j) i)
  let P (s : ℝ) (j : Fin d) := project β (A s j 0) (A s j 1)
  have acont (j i) : Continuous (fun s => A s j i) := by dsimp [A,gm]; fun_prop
  have apos (s j i) : 0<A s j i := Real.exp_pos _
  have ap (j i) := hb.trans_le (fac_mem h1.le (hp j) i).1
  have ar (j i) := hb.trans_le (fac_mem h1.le (hr j) i).1
  have amem s (hs : s∈Icc (0:ℝ) 1) j i : A s j i∈Icc β 1 :=
    gm_bounds hs hb (fac_mem h1.le (hp j) _) (fac_mem h1.le (hr j) _)
  have pvalid s (hs : s∈Icc (0:ℝ) 1) j : simplexN (P s j) := project_simplex hb h1 (amem s hs j 0) (amem s hs j 1)
  have sc (j) : Continuous (fun s => stretch β (A s j 0) (A s j 1)) := by
    apply continuous_const.max
    exact continuous_const.div ((acont j 0).add (acont j 1)) (fun s => (add_pos (apos s j 0) (apos s j 1)).ne')
  have pc j i : Continuous (fun s => P s j i) := by
    fin_cases i
    · exact (continuous_const.sub ((sc j).mul (acont j 0))).div_const _
    · exact (continuous_const.sub ((sc j).mul (acont j 1))).div_const _
    · exact (((sc j).mul ((acont j 0).add (acont j 1))).sub continuous_const).div_const _
  have P0 : P 0=p := by
    funext j; dsimp [P,A]; rw [gm_zero (ap _ _),gm_zero (ap _ _),project_restore hb h1 (hp j)]
  have P1 : P 1=r := by
    funext j; dsimp [P,A]; rw [gm_one (ar _ _),gm_one (ar _ _),project_restore hb h1 (hr j)]
  let height (s : ℝ) := rawWeight β (P s) 2/rawWeight β (P s) 1
  have hc : ContinuousOn height (Icc 0 1) :=
    (raw_cont β P pc 2).continuousOn.div (raw_cont β P pc 1).continuousOn
      (fun s hs => (raw_pos (pvalid s hs) hb h1.le 1).ne')
  obtain ⟨s,hs,hy⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc
    (show W∈Icc (height 0) (height 1) by simpa only [height,P0,P1] using And.intro lo hi)
  refine ⟨P s,pvalid s hs,?_,(div_eq_iff (raw_pos (pvalid s hs) hb h1.le 1).ne').mp hy⟩
  have pa (i) : (∏ j,A s j i)=gm s (rawWeight β p i) (rawWeight β r i) :=
    prod_gm s _ _ (fun j => ap j i) (fun j => ar j i)
  have rat : (∏ j,A s j 0)=R*(∏ j,A s j 1) := by
    rw [pa,pa,ep,er,gm_scale s hR (raw_pos hp hb h1.le 1) (raw_pos hr hb h1.le 1)]
  simp only [rawWeight,P,project_f0 h1,project_f1 h1,prod_mul_distrib,rat]
  ring

end
end PottsBP.Classification
