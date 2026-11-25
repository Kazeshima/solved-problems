import PottsClassColumn

namespace PottsBP
open Finset Set
open scoped BigOperators
noncomputable section
namespace Classification

lemma normalized_sum_mem {q d : ℕ} {β : ℝ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Fin q → ℝ) (hr : ∀ a, Realizes q d β (g a)) (hz : ∀ a, 0 < total (g a))
    (hc : Convex ℝ (generalImage q d β)) : normVec (fun i => ∑ a,g a i) ∈ generalImage q d β := by
  classical
  let T := ∑ a,total (g a)
  have hT : 0 < T := sum_pos (fun a _ => hz a) univ_nonempty
  have hsum : (∑ a,total (g a)/T) = 1 := by rw [← sum_div]; exact div_self hT.ne'
  have H := hc.sum_mem (fun a _ => (div_pos (hz a) hT).le) hsum (fun a _ => (hr a).mem (hz a))
  have ht : total (fun i => ∑ a,g a i) = T := sum_comm
  convert H using 1
  ext i
  simp only [normVec,ht,sum_apply,Pi.smul_apply,smul_eq_mul,sum_div]
  apply sum_congr rfl; intro a _
  field_simp [(hz a).ne']
  ring

lemma realizes_pins {q d : ℕ} (β : ℝ) (f : Fin d ↪ Fin q) :
    Realizes q d β (fun i => if (∃ j, f j=i) then β else 1) := by
  classical
  refine ⟨fun j i => if f j=i then 1 else 0,fun j => singleton_pin _,?_⟩
  funext i
  calc
    _ = ∏ j,if f j=i then β else 1 := by
      apply prod_congr rfl; intro j _
      by_cases h : f j=i <;> simp [h]
    _ = _ := Fintype.prod_ite_eq_ite_exists _ (fun _ _ a b => f.injective (a.trans b.symm)) β

lemma column_sum_all {q d : ℕ} (p : Fin d → Fin q → ℝ) (hp : ∀ j,simplexN (p j)) :
    (∑ i,∑ j,p j i) = (d:ℝ) := by rw [sum_comm]; simp [fun j => (hp j).2]

theorem nonconvex_positive {q d : ℕ} (hq : 4 ≤ q) (hd : 2 ≤ d)
    {β : ℝ} (hb : 0 < β) (h1 : β < 1) : ¬ Convex ℝ (generalImage q d β) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
  let e : Fin 3 ↪ Fin q := Fin.castLEEmb (by omega)
  let A := (univ : Finset (Fin 3)).map e
  let b (i : Fin q) : ℕ := if e 0=i then k else 0
  let f (m : Fin 3) := (Fin.succAboveEmb m).trans e
  let g (m : Fin 3) (i : Fin q) := (pinFactor β (e 0) i)^k * (if (∃ j, f m j=i) then β else 1)
  have hr (m) : Realizes q (2+k) β (g m) := add_pins (realizes_pins β (f m)) (e 0) k
  have gpos (m i) : 0 < g m i := by
    dsimp [g,pinFactor]
    split <;> split <;> positivity
  letI : NeZero q := ⟨by omega⟩
  have hz (m) := total_pos_of_pos (gpos m)
  let H (i : Fin q) := ∑ m,g m i
  have hT : 0 < total H := total_pos_of_pos (fun i => sum_pos (fun m _ => gpos m i) univ_nonempty)
  have band (i) : pinFactor β (e 0) i ^ k = β^(b i) := by
    by_cases hi : e 0=i <;> simp [b,pinFactor,hi]
  have active (i) (hi : i∈A) : H i = β^(b i)*(1+2*β) := by
    obtain ⟨l,_,rfl⟩ := mem_map.mp hi
    have used (m : Fin 3) : (∃ j, f m j=e l) ↔ l≠m := by
      change (∃ j,e (m.succAbove j)=e l) ↔ _
      simp only [EmbeddingLike.apply_eq_iff_eq]
      exact Fin.exists_succAbove_eq_iff
    calc
      _ = ∑ m : Fin 3, β^(b (e l))*(β+(if l=m then 1-β else 0)) := by
        apply sum_congr rfl; intro m _
        change pinFactor β (e 0) (e l)^k*(if (∃ j,f m j=e l) then β else 1) = _
        rw [band, if_congr (used m) rfl rfl]
        by_cases ht : l=m
        · rw [if_neg (not_not.mpr ht),if_pos ht]; ring
        · rw [if_pos ht,if_neg ht]; ring
      _ = _ := by
        rw [← mul_sum]
        congr 1
        rw [sum_add_distrib]
        simp
        ring
  have inactive (i) (hi : i∉A) : H i=3 := by
    have he (m : Fin 3) : e m ≠ i := fun h => hi (mem_map.mpr ⟨m,mem_univ _,h⟩)
    have hu (m : Fin 3) : ¬∃ j, f m j=i := by rintro ⟨j,h⟩; exact he _ h
    simp [H,g,hu,pinFactor,he]
  let o : Fin q := ⟨3,by omega⟩
  have ho : o∉A := by
    rintro h; obtain ⟨m,_,hm⟩ := mem_map.mp h
    have hv := congrArg Fin.val hm
    change m.val=3 at hv
    omega
  intro hc
  have hw := normalized_sum_mem g hr hz hc
  obtain ⟨p,hp,hS,heq⟩ := hw
  let S := ∑ i,rawWeight β p i
  let t := 1-β
  have ht : 0 < t := sub_pos.mpr h1
  have hwgt (i) : rawWeight β p i = (H i/total H)*S :=
    (div_eq_iff hS.ne').mp (congrFun heq i)
  have eqcol (i) (hi : i∈A) :
      rawWeight β p i = β^(b i)*(1-t*(2/3))*rawWeight β p o := by
    rw [hwgt i,hwgt o,active i hi,inactive o ho]; dsimp [t]; ring
  have upper (i) (hi : i∈A) : rawWeight β p i ≤ β^(b i)*(1-t*(2/3)) := by
    rw [eqcol i hi]
    have hn : 0 ≤ 1-t*(2/3) := by dsimp [t]; linarith
    exact mul_le_of_le_one_right (mul_nonneg (pow_nonneg hb.le _) hn) (raw_le_one hp hb.le h1.le o)
  let u (i : Fin q) := (b i:ℝ)+(if i∈A then (2/3:ℝ) else 0)
  have ui (i) (hi : i∈A) : u i=(b i:ℝ)+2/3 := by simp [u,hi]
  have uo (i) (hi : i∉A) : u i=0 := by
    have h : e 0≠i := fun h => hi (mem_map.mpr ⟨0,mem_univ _,h⟩)
    simp [u,b,hi,h]
  have su : (∑ i,u i) = (2+k:ℕ) := by
    have hB : (∑ i,(b i:ℝ)) = k := by simp [b,apply_ite]
    simp only [u,sum_add_distrib,hB]
    have hA : A.card=3 := by simp [A]
    simp [sum_ite,hA]; ring
  have lower (i) : β^(b i)*(1+t*((b i:ℝ)-∑ j,p j i)) ≤ rawWeight β p i :=
    column_tangent univ _ hb.le h1.le (fun j => (hp j).1 _) (fun j => simplexN_le_one (hp j) i) (b i)
  have mass (i) : u i ≤ ∑ j,p j i := by
    by_cases hi : i∈A
    · have hh := (mul_le_mul_left (pow_pos hb (b i))).mp ((lower i).trans (upper i hi))
      rw [ui i hi]
      have H' : t*((b i:ℝ)-(∑ j,p j i)) ≤ t*(-(2/3)) := by linarith only [hh]
      have := (mul_le_mul_left ht).mp H'
      linarith
    · rw [uo i hi]; exact sum_nonneg fun j _ => (hp j).1 _
  have exactMass (i) : (∑ j,p j i)=u i := by
    apply le_antisymm _ (mass i)
    apply le_of_not_gt
    intro h
    have hh := sum_lt_sum (fun i _ => mass i) ⟨i,mem_univ _,h⟩
    rw [su,column_sum_all p hp] at hh
    exact (lt_irrefl _) hh
  have fractional (j i) (hji : 0 < p j i) (hji' : p j i < 1) : p j i=2/3 := by
    by_cases hi : i∈A
    · have hm := exactMass i
      rw [ui i hi] at hm
      have tight : rawWeight β p i = β^(b i)*(1+t*((b i:ℝ)-∑ j,p j i)) := by
        apply le_antisymm _ (lower i)
        rw [hm,show 1+t*((b i:ℝ)-((b i:ℝ)+2/3))=1-t*(2/3) by ring]
        exact upper i hi
      have h := fractional_at_tangent _ hb h1 (fun l => (hp l).1 i)
        (fun l => simplexN_le_one (hp l) i) (b i) tight j hji hji'
      rw [hm] at h; linarith
    · have h := single_le_sum (s:=univ) (f:=fun l => p l i) (fun l _ => (hp l).1 i) (mem_univ j)
      rw [exactMass i,uo i hi] at h; linarith
  have he1 : e 1∈A := mem_map.mpr ⟨1,mem_univ _,rfl⟩
  have hb1 : b (e 1)=0 := by simp [b]
  have hm1 := exactMass (e 1)
  rw [ui _ he1,hb1] at hm1
  norm_num at hm1
  have ex : ∃ j,0<p j (e 1) := by
    apply Classical.byContradiction
    intro h
    have hzero (j) := le_antisymm (le_of_not_gt (fun hj => h ⟨j,hj⟩)) ((hp j).1 (e 1))
    simp only [hzero,sum_const_zero] at hm1
    norm_num at hm1
  obtain ⟨j,hj⟩ := ex
  have hsmall := single_le_sum (s:=univ) (f:=fun l => p l (e 1)) (fun l _ => (hp l).1 _) (mem_univ j)
  have hv := fractional j (e 1) hj (by linarith)
  have onlyone (i : Fin q) (_ : i∈(univ : Finset (Fin q))) (hne : i≠e 1) : p j i=0 := by
    have pair := sum_le_sum_of_subset_of_nonneg (s:={i,e 1}) (t:=univ)
      (subset_univ _) (fun l _ _ => (hp j).1 l)
    rw [sum_pair hne,(hp j).2,hv] at pair
    apply Classical.byContradiction
    intro hn
    have := fractional j i (lt_of_le_of_ne ((hp j).1 i) (Ne.symm hn)) (by linarith)
    linarith
  have Hrow : (∑ i,p j i)=p j (e 1) := sum_eq_single (e 1) onlyone (by simp)
  rw [(hp j).2,hv] at Hrow
  norm_num at Hrow

end Classification
open Classification

theorem source_nonconvex_positive_beta {q d : ℕ} (hq : 4 ≤ q) (hd : 2 ≤ d)
    {β : ℝ} (hb : 0 < β) (h1 : β < 1) : ¬ Convex ℝ (admissibleSourceImage q d β) := by
  rw [admissibleSourceImage_eq_generalImage]
  exact nonconvex_positive hq hd hb h1

end
end PottsBP
