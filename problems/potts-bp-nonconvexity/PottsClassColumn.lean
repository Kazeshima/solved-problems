import PottsClassBasic

namespace PottsBP.Classification
open Finset
open scoped BigOperators
noncomputable section

private lemma tangent_empty (β : ℝ) (hb : 0 ≤ β) (b : ℕ) :
    β^b*(1+(1-β)*(b:ℝ)) ≤ 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h : β*(1+(1-β)*((b:ℝ)+1)) ≤ 1+(1-β)*b := by
      nlinarith only [mul_nonneg (sq_nonneg (1-β)) (show (0:ℝ) ≤ b+1 by positivity)]
    rw [pow_succ,Nat.cast_succ,mul_assoc]
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg hb _)).trans ih

/-- The line through the values at adjacent integer occupancies supports every column. -/
theorem column_tangent {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {β : ℝ} (hb : 0 ≤ β) (h1 : β ≤ 1) (v0 : ∀ j, 0 ≤ v j) (v1 : ∀ j, v j ≤ 1) (b : ℕ) :
    β^b*(1+(1-β)*((b:ℝ)-∑ j ∈ s, v j)) ≤ ∏ j ∈ s,(1-(1-β)*v j) := by
  induction s using Finset.induction_on generalizing b with
  | empty => simpa using tangent_empty β hb b
  | @insert i s hi ih =>
    cases b with
    | zero =>
      have h := product_lower (insert i s) (fun j => (1-β)*v j)
        (fun j => mul_nonneg (sub_nonneg.mpr h1) (v0 j))
        (fun j => mul_le_one₀ (by linarith) (v0 j) (v1 j))
      simpa [← mul_sum,sub_eq_add_neg] using h
    | succ b =>
      rw [sum_insert hi,prod_insert hi,Nat.cast_succ]
      let U := ∑ j ∈ s,v j
      let R := ∏ j ∈ s,(1-(1-β)*v j)
      have hu : β^(b+1)*(1+(1-β)*((b:ℝ)+1-U)) ≤ R := by simpa [U,R] using ih (b+1)
      have hd : β^b*(1+(1-β)*((b:ℝ)-U)) ≤ R := ih b
      calc
        _ = (1-v i)*(β^(b+1)*(1+(1-β)*((b:ℝ)+1-U))) +
              (v i*β)*(β^b*(1+(1-β)*((b:ℝ)-U))) := by dsimp [U]; rw [pow_succ]; ring
        _ ≤ (1-v i)*R+(v i*β)*R := add_le_add (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr (v1 i)))
              (mul_le_mul_of_nonneg_left hd (mul_nonneg (v0 i) hb))
        _ = _ := by change _ = (1-(1-β)*v i)*R; ring

/-- At equality any fractional cell has precisely the excess of column mass over b. -/
theorem fractional_at_tangent {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ)
    {β : ℝ} (hb : 0 < β) (h1 : β < 1) (v0 : ∀ j, 0 ≤ v j) (v1 : ∀ j, v j ≤ 1)
    (b : ℕ) (tight : (∏ j,(1-(1-β)*v j)) = β^b*(1+(1-β)*((b:ℝ)-∑ j,v j)))
    (i : ι) (hi0 : 0 < v i) (hi1 : v i < 1) : v i = (∑ j,v j)-(b:ℝ) := by
  let s := (univ : Finset ι).erase i
  let U := ∑ j ∈ s,v j
  let R := ∏ j ∈ s,(1-(1-β)*v j)
  have atc (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      β^b*(1+(1-β)*((b:ℝ)-(c+U))) ≤ (1-(1-β)*c)*R := by
    let z := Function.update v i c
    have z0 (j) : 0 ≤ z j := by by_cases hj : j=i <;> simp [z,hj,hc0,v0]
    have z1 (j) : z j ≤ 1 := by by_cases hj : j=i <;> simp [z,hj,hc1,v1]
    have h := column_tangent univ z hb.le h1.le z0 z1 b
    rw [← add_sum_erase univ z (mem_univ i),
        ← mul_prod_erase univ (fun j => 1-(1-β)*z j) (mem_univ i)] at h
    have sm : (∑ j ∈ s,z j)=U := sum_congr rfl fun j hj =>
      Function.update_of_ne (ne_of_mem_erase hj) c v
    have pr : (∏ j ∈ s,(1-(1-β)*z j))=R := by
      apply prod_congr rfl; intro j hj
      simp [z,ne_of_mem_erase hj]
    change β^b*(1+(1-β)*((b:ℝ)-(z i+(∑ j ∈ s,z j)))) ≤
      (1-(1-β)*z i)*(∏ j ∈ s,(1-(1-β)*z j)) at h
    simpa only [sm,pr,z,Function.update_self] using h
  have su : v i+U = ∑ j,v j := add_sum_erase univ v (mem_univ i)
  have pu : (1-(1-β)*v i)*R = ∏ j,(1-(1-β)*v j) :=
    mul_prod_erase univ (fun j => 1-(1-β)*v j) (mem_univ i)
  rw [← su,← pu] at tight
  let D (c : ℝ) := (1-(1-β)*c)*R-β^b*(1+(1-β)*((b:ℝ)-(c+U)))
  have hD0 : 0 ≤ D 0 := sub_nonneg.mpr (atc 0 le_rfl zero_le_one)
  have hD1 : 0 ≤ D 1 := sub_nonneg.mpr (atc 1 zero_le_one le_rfl)
  have hm : (1-v i)*D 0+v i*D 1=0 := by dsimp [D]; linear_combination tight
  obtain ⟨e0,e1⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg (sub_nonneg.mpr hi1.le) hD0)
    (mul_nonneg hi0.le hD1)).mp hm
  have d0 := (mul_eq_zero.mp e0).resolve_left (sub_ne_zero.mpr hi1.ne')
  have d1 := (mul_eq_zero.mp e1).resolve_left hi0.ne'
  dsimp [D] at d0 d1
  have hR : R=β^b := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr h1.ne') : (1-β)*R = (1-β)*β^b → _)
    linear_combination d0-d1
  have hU : (b:ℝ)-U=0 := by
    apply (mul_eq_zero.mp (show (β^b*(1-β))*((b:ℝ)-U)=0 by
      rw [hR] at d0; linear_combination -d0)).resolve_left
    exact mul_ne_zero (pow_ne_zero _ hb.ne') (sub_ne_zero.mpr h1.ne')
  linarith only [su,hU]

end
end PottsBP.Classification
