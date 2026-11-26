import Quadric.Orbit
import Quadric.GaugeClasses

namespace Quadric.Four
open Finset
open scoped BigOperators
attribute [local irreducible] points pairs lines bad violations level height

noncomputable def countType (k : Fin 10) : ℕ := (univ.filter (fun o : Opt => height o=k)).card

theorem direction_count : Fintype.card Direction=15 := by
  rw [Fintype.card_of_subtype ((univ : Finset W).erase 0) (by simp)]
  norm_num [Fintype.card_pi]

theorem count_nine : countType 9=16384 := by
  classical
  have inner (s : Opt) :
      ∑ x, (if level s x=9 then (1:ℕ) else 0) = if height s=9 then 1 else 0 := by
    by_cases hs : height s=9
    · obtain ⟨x,hx⟩ := heavy_exists s
      have h9 := hx.trans hs
      have eq' (y : W) : level s y=9 ↔ y=x := by
        constructor
        · intro hy; by_contra hne
          have := nine_others h9 hne
          rw [hy] at this
          exact (by decide : (9:Fin 10)≠1) this
        · rintro rfl; exact h9
      simp only [eq',sum_ite_eq',mem_univ,if_true,if_pos hs]
    · have h (x : W) : level s x≠9 := fun hh => hs (nine_height hh)
      simp [hs,h]
  calc
    _ = ∑ s : Opt, (if height s=9 then (1:ℕ) else 0) := by simp [countType,sum_boole]
    _ = ∑ s : Opt, ∑ x : W, (if level s x=9 then (1:ℕ) else 0) :=
      sum_congr rfl fun s _ => (inner s).symm
    _ = ∑ x : W, ∑ s : Opt, (if level s x=9 then (1:ℕ) else 0) := sum_comm
    _ = ∑ _x : W, (1024:ℕ) := by
      apply sum_congr rfl; intro x _
      rw [sum_boole]
      simpa only [HeavyAt,Fintype.card_subtype,Nat.cast_id] using heavy_at_count x
    _ = _ := by norm_num [Fintype.card_pi]

theorem light_count_dirs {s : Opt} {x : W} (hx : level s x=8) :
    (univ.filter fun a : Direction => height (step a s)=9).card=8 := by
  classical
  let L := univ.filter fun a : Direction => height (step a s)=9
  let R := univ.filter fun y : W => level s y=2
  have eqcard : L.card=R.card := by
    apply card_bij (fun a _ => x+a.val)
    · intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(step_eight hx a).1.mp (mem_filter.mp ha).2⟩
    · intro a _ b _ h; exact Subtype.ext (add_left_cancel h)
    · intro y hy
      have h2 := (mem_filter.mp hy).2
      have hne : x≠y := by rintro rfl; rw [hx] at h2; contradiction
      let a : Direction := ⟨x+y,mt (word_zero x y).mp hne⟩
      have hr : x+a.val=y := by dsimp [a]; simp [←add_assoc]
      exact ⟨a,mem_filter.mpr ⟨mem_univ _,(step_eight hx a).1.mpr (hr ▸ h2)⟩,hr⟩
  exact eqcard.trans (count_light hx)

theorem entering_nine (s : Opt) :
    (∑ a : Direction, if height (step a s)=9 then (1:ℕ) else 0) =
    if height s = 8 then 8 else 0 := by
  classical
  by_cases hs : height s=8
  · obtain ⟨x,hx⟩ := heavy_exists s
    simp only [sum_boole,if_pos hs,Nat.cast_id]
    exact light_count_dirs (hx.trans hs)
  · have no (a : Direction) : height (step a s) ≠ 9 := by
      intro hh
      have hm := step_nine a hh
      rw [step_involutive a s] at hm
      exact hs hm
    simp [hs,no]

theorem incidence_count : 15*countType 9 = 8*countType 8 := by
  classical
  have swap (a : Direction) : (∑ s : Opt, if height (step a s)=9 then (1:ℕ) else 0) =
      ∑ s : Opt, if height s=9 then (1:ℕ) else 0 :=
    Equiv.sum_comp (step_involutive a).toPerm (fun s => if height s=9 then 1 else 0)
  calc
    _ = ∑ _a : Direction, ∑ s : Opt, if height s=9 then (1:ℕ) else 0 := by
      simp [sum_boole,countType,direction_count]
    _ = ∑ a : Direction, ∑ s : Opt, if height (step a s)=9 then (1:ℕ) else 0 :=
      sum_congr rfl fun a _ => (swap a).symm
    _ = ∑ s : Opt, ∑ a : Direction, if height (step a s)=9 then (1:ℕ) else 0 := sum_comm
    _ = _ := by
      simp_rw [entering_nine]
      have he (s : Opt) : (if height s=8 then (8:ℕ) else 0) =
          8*(if height s=8 then 1 else 0) := by split_ifs <;> decide
      simp_rw [he,← mul_sum,sum_boole]; rfl

/-- Exact cardinality of optimal assignments on the 135 genuine quadric points. -/
theorem optimal_assignments_count : Fintype.card Opt = 61440 := by
  classical
  let a : Direction := ⟨axis 0,axis_ne _⟩
  let I (s : Opt) : ℕ := if height s=8 then 1 else 0
  have local_count (s : Opt) : I s + I (step a s)=1 := by
    rcases profiles s with hs|hs|hs
    · simp [I,hs,step_nine a hs]
    · obtain ⟨x,hx⟩ := heavy_exists s
      have h8 := hx.trans hs
      have hd := step_eight h8 a
      rcases eight_others h8 (partner_ne a x) with h|h
      · simp [I,hs,hd.2.mpr h]
      · simp [I,hs,hd.1.mpr h]
    · simp [I,hs,step_four a hs]
  have hs : (∑ s : Opt, (I s + I (step a s))) = ∑ _s : Opt, (1:ℕ) :=
    sum_congr rfl (fun s _ => local_count s)
  have hi : ∑ s, I s=countType 8 := by simp [I,countType,sum_boole]
  have hperm := Equiv.sum_comp (step_involutive a).toPerm I
  change (∑ s, I (step a s)) = ∑ s, I s at hperm
  rw [sum_add_distrib,hperm,hi] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hs
  have h := incidence_count
  rw [count_nine] at h
  have h8 : countType 8=30720 := by omega
  rw [h8] at hs
  simpa only [Nat.cast_id, Nat.reduceAdd] using hs.symm

/-- Distinct violated-line sets, with labelled sign assignments identified exactly by their
eight-bit gauge. -/
theorem optimal_configurations_count : configurations.card=240 := by
  have h := gauge_counting
  rw [optimal_assignments_count] at h
  omega

end Quadric.Four
