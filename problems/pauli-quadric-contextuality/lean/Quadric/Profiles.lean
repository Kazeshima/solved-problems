import Quadric.Mixing

namespace Quadric.Four
open Finset
open scoped BigOperators
attribute [local irreducible] points pairs lines bad violations level
set_option maxRecDepth 4096

noncomputable def height (s : Opt) : Fin 10 :=
  (univ.image (level s)).max' (univ_nonempty.image _)
theorem level_le (s : Opt) (x : W) : level s x ≤ height s :=
  le_max' _ _ (mem_image_of_mem _ (mem_univ x))
theorem heavy_exists (s : Opt) : ∃ x, level s x=height s := by
  obtain ⟨x,_,h⟩ := mem_image.mp (max'_mem (univ.image (level s)) (univ_nonempty.image _))
  exact ⟨x,h⟩

attribute [local irreducible] height

theorem level_sum (s : Opt) : ∑ x, (level s x).val = 24 := by
  have h := weight_sum s
  simp_rw [level_spec] at h; exact_mod_cast h

theorem level_squares (s : Opt) : ∑ x, (level s x).val^2 = 96 := by
  have h := weight_squares s.val
  simp_rw [level_spec s] at h; exact_mod_cast h

theorem profiles (s : Opt) : height s=9 ∨ height s=8 ∨ height s=4 := by
  classical
  obtain ⟨x,hx⟩ := heavy_exists s
  by_contra! hn
  have hm : 3 < (height s).val := by
    by_contra! hh
    have h : ∑ y, (level s y).val^2 ≤ ∑ y, 3*(level s y).val :=
      sum_le_sum fun i _ => by
        have hle : (level s i).val ≤ (height s).val := level_le s i
        simpa only [sq] using Nat.mul_le_mul_right (level s i).val (hle.trans hh)
    rw [level_squares,← mul_sum,level_sum] at h
    omega
  have test : ∀ m j : Fin 10, 3<m.val → m≠9 → m≠8 → m≠4 →
      j≤m → Compatible m j → j=0 := by decide +kernel
  have off (y) (hy : y≠x) : level s y=0 := by
    apply test (height s) _ hm hn.1 hn.2.1 hn.2.2 (level_le s _)
    rw [←hx]; exact compatible_coords s (Ne.symm hy)
  have re (y : W) : (level s y).val = if y=x then (height s).val else 0 := by
    by_cases hy : y=x <;> simp [hy,hx,off]
  have h := level_sum s; simp_rw [re] at h
  simp only [sum_ite_eq',mem_univ,if_true] at h
  have := (height s).isLt; omega

theorem nine_others {s : Opt} {x y : W} (hx : level s x=9) (hy : y≠x) : level s y=1 := by
  have h := compatible_coords s (Ne.symm hy)
  rw [hx] at h
  exact (by decide +kernel : ∀ j : Fin 10, Compatible 9 j → j=1) _ h

theorem eight_others {s : Opt} {x y : W} (hx : level s x=8) (hy : y≠x) :
    level s y=0 ∨ level s y=2 := by
  have h := compatible_coords s (Ne.symm hy)
  rw [hx] at h
  exact (by decide +kernel : ∀ j : Fin 10, Compatible 8 j → j=0 ∨ j=2) _ h

theorem nine_height {s : Opt} {x : W} (hx : level s x=9) : height s=9 := by
  have h := level_le s x; rw [hx] at h
  exact Fin.ext (by omega)

theorem eight_height {s : Opt} {x : W} (hx : level s x=8) : height s=8 := by
  rcases profiles s with h|h|h
  · obtain ⟨y,hy⟩ := heavy_exists s
    have h9 := hy.trans h
    have hxy : x≠y := by rintro rfl; rw [hx] at h9; exact (by decide : (8:Fin 10)≠9) h9
    have h' := nine_others h9 hxy; rw [hx] at h'; contradiction
  · exact h
  · have hl := level_le s x; rw [hx,h] at hl; exact False.elim ((by decide : ¬((8:Fin 10)≤4)) hl)

theorem four_others {s : Opt} (h : height s=4) (y : W) :
    level s y=0 ∨ level s y=4 := by
  obtain ⟨x,hx⟩ := heavy_exists s
  by_cases he : x=y
  · right; simpa [←he] using hx.trans h
  · have hc := compatible_coords s he
    have hl := level_le s y
    rw [hx,h] at hc; rw [h] at hl
    exact (by decide +kernel : ∀ j : Fin 10, j≤4 → Compatible 4 j → j=0 ∨ j=4) _ hl hc

theorem four_height {s : Opt} {x : W} (hx : level s x=4) : height s=4 := by
  rcases profiles s with h|h|h
  · obtain ⟨y,hy⟩ := heavy_exists s
    have hc := hy.trans h
    by_cases e : x=y
    · rw [←e,hx] at hc; contradiction
    · have hh := nine_others hc e; rw [hx] at hh; contradiction
  · obtain ⟨y,hy⟩ := heavy_exists s
    have hc := hy.trans h
    by_cases e : x=y
    · rw [←e,hx] at hc; contradiction
    · have hh := eight_others hc e; rw [hx] at hh; exact False.elim ((by decide : ¬((4:Fin 10)=0 ∨ (4:Fin 10)=2)) hh)
  · exact h

theorem partner_ne (a : Direction) (x : W) : x+a.val ≠ x := by
  intro h; exact a.property (by simpa using h)

theorem step_nine (a : Direction) {s : Opt} (hh : height s=9) : height (step a s)=8 := by
  obtain ⟨x,hx⟩ := heavy_exists s
  have h9 := hx.trans hh
  have h1 := nine_others h9 (partner_ne a x)
  have hm := mix_levels a s x
  rw [h9,h1] at hm
  rcases (by decide +kernel : ∀ b c : Fin 10, PairCode 9 1 b c → b=8 ∨ c=8) _ _ hm with h|h
  · exact eight_height h
  · exact eight_height h

theorem step_eight {s : Opt} {x : W} (hx : level s x=8) (a : Direction) :
    (height (step a s)=9 ↔ level s (x+a.val)=2) ∧
    (height (step a s)=4 ↔ level s (x+a.val)=0) := by
  have hm := mix_levels a s x
  rw [hx] at hm
  rcases eight_others hx (partner_ne a x) with h|h
  · rw [h] at hm ⊢
    have r := (by decide +kernel : ∀ b c : Fin 10, PairCode 8 0 b c → b=4) _ _ hm
    rw [four_height r]; decide
  · rw [h] at hm ⊢
    rcases (by decide +kernel : ∀ b c : Fin 10, PairCode 8 2 b c → b=9 ∨ c=9) _ _ hm with h9|h9 <;>
      rw [nine_height h9] <;> decide

theorem step_four (a : Direction) {s : Opt} (hh : height s=4) : height (step a s)=8 := by
  obtain ⟨x,hx⟩ := heavy_exists (step a s)
  have hm := mix_levels a s x
  have hout : (level (step a s) x)=0 ∨ level (step a s) x=2 ∨ level (step a s) x=8 :=
    (by decide +kernel : ∀ m j b c : Fin 10,
      (m=0 ∨ m=4) → (j=0 ∨ j=4) → PairCode m j b c → b=0 ∨ b=2 ∨ b=8)
      _ _ _ _ (four_others hh x) (four_others hh _) hm
  rw [hx] at hout
  rcases profiles (step a s) with h|h|h <;> simp_all

theorem count_light {s : Opt} {x : W} (hx : level s x=8) :
    (univ.filter fun y => level s y=2).card = 8 := by
  classical
  have ht (y : W) : (level s y).val =
      (if y=x then 8 else 0) + 2*(if level s y=2 then 1 else 0) := by
    by_cases h : y=x
    · subst y; rw [hx,if_pos rfl]; decide
    · rcases eight_others hx h with h'|h' <;> simp [h,h']
  have h : 8 + 2*(univ.filter fun y => level s y=2).card = 24 := by
    calc
      _ = ∑ y, ((if y=x then (8:ℕ) else 0) + 2*(if level s y=2 then 1 else 0)) := by
        rw [sum_add_distrib,←mul_sum,sum_boole,sum_ite_eq',if_pos (mem_univ _)]
        rfl
      _ = _ := (sum_congr rfl fun y _ => (ht y).symm).trans (level_sum s)
  omega

end Quadric.Four
