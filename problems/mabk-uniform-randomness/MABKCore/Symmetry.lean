import MABKCore.Basic

namespace MABK

open Finset Set
open scoped BigOperators ComplexConjugate
noncomputable section

/-- A symmetric multiaffine polynomial on a finite set of coordinates. -/
def polarization {ι : Type*} (s : Finset ι) (c : ℕ → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ t ∈ s.powerset, c t.card * ∏ i ∈ t, z i

private theorem polar_insert {ι : Type*} [DecidableEq ι] {s : Finset ι} {i : ι}
    (hi : i ∉ s) (c : ℕ → ℂ) (z : ι → ℂ) :
    polarization (insert i s) c z =
      polarization s c z + z i * polarization s (fun k => c (k+1)) z := by
  unfold polarization
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h => hi ((Finset.mem_powerset.mp ht) h)
  rw [Finset.card_insert_of_not_mem hit, Finset.prod_insert hit]
  ring

private theorem polar_congr {ι : Type*} {s : Finset ι} (c : ℕ → ℂ)
    {z w : ι → ℂ} (h : ∀ i ∈ s, z i = w i) :
    polarization s c z = polarization s c w := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_congr rfl (fun i hi => h i ((Finset.mem_powerset.mp ht) hi))]

private def replacePair {ι : Type*} [DecidableEq ι] (z : ι → Circle)
    (i j : ι) (p q : Circle) : ι → Circle :=
  Function.update (Function.update z i p) j q

private theorem pair_section {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ → ℂ) (z : ι → Circle) (i j : ι) (hij : i ≠ j) :
    ∃ A B C : ℂ, ∀ p q : Circle,
      polarization univ c (fun k => (replacePair z i j p q k : ℂ)) =
      A + B*((p:ℂ)+q) + C*(p:ℂ)*q := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s, hij]
  have hj : j ∉ s := by simp [s]
  have hall : (univ : Finset ι) = insert i (insert j s) := by
    simp [s, Finset.insert_erase (show j ∈ univ.erase i by simp [hij.symm])]
  let w : ι → ℂ := fun k => z k
  refine ⟨polarization s c w, polarization s (fun k => c (k+1)) w,
    polarization s (fun k => c (k+1+1)) w, ?_⟩
  intro p q
  have hkeep (b : ℕ → ℂ) :
      polarization s b (fun k => (replacePair z i j p q k : ℂ)) = polarization s b w := by
    apply polar_congr
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    simp [replacePair, Function.update_of_ne, hkj, hki, w]
  rw [hall, polar_insert (by simp [hij, hi]), polar_insert hj, polar_insert hj]
  simp only [hkeep]
  simp only [replacePair, Function.update_self, Function.update_of_ne hij]
  ring

private theorem pair_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Circle) (i j : ι) (hij : i ≠ j) :
    ∃ A : ℂ, ∀ p q : Circle, (∑ k, (replacePair z i j p q k : ℂ)) = A + p + q := by
  let s := (univ.erase i).erase j
  have hi : i ∉ s := by simp [s, hij]
  have hj : j ∉ s := by simp [s]
  have hall : (univ : Finset ι) = insert i (insert j s) := by
    simp [s, Finset.insert_erase (show j ∈ univ.erase i by simp [hij.symm])]
  refine ⟨∑ k ∈ s, (z k:ℂ), ?_⟩
  intro p q
  rw [hall, Finset.sum_insert (by simp [hij, hi]), Finset.sum_insert hj]
  have hsum : (∑ k ∈ s, (replacePair z i j p q k : ℂ)) = ∑ k ∈ s, (z k:ℂ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    simp [replacePair, Function.update_of_ne, hkj, hki]
  rw [hsum]
  simp [replacePair, hij, add_comm, add_left_comm, add_assoc]

private def chord (l : ℝ) (a b : ℂ) := ((1-l : ℝ):ℂ)*a + (l:ℂ)*b

private theorem chord_sq (l : ℝ) (a b : ℂ) :
    ‖chord l a b‖^2 =
      (1-l)*‖a‖^2 + l*‖b‖^2 - l*(1-l)*‖a-b‖^2 := by
  simp [chord, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem endpoints_eq {l m : ℝ} {a b : ℂ} (hl : 0 < l) (hl' : l < 1)
    (h : m = ‖chord l a b‖^2) (ha : ‖a‖^2 ≤ m) (hb : ‖b‖^2 ≤ m) :
    ‖a‖^2 = m ∧ ‖b‖^2 = m := by
  rw [chord_sq] at h
  have hg := mul_nonneg (mul_nonneg hl.le (sub_nonneg.mpr hl'.le)) (sq_nonneg ‖a-b‖)
  have hA := mul_nonneg (sub_nonneg.mpr hl'.le) (sub_nonneg.mpr ha)
  have hB := mul_nonneg hl.le (sub_nonneg.mpr hb)
  constructor
  · rcases ha.lt_or_eq with hlt | heq
    · nlinarith only [h, hg, hB, mul_pos (sub_pos.mpr hl') (sub_pos.mpr hlt)]
    · exact heq
  · rcases hb.lt_or_eq with hlt | heq
    · nlinarith only [h, hg, hA, mul_pos hl (sub_pos.mpr hlt)]
    · exact heq

/-- Midpoint direction and chord parameter for two distinct unit phases.
This construction also applies to opposite phases. -/
private theorem pair_chord (p q : Circle) (hpq : p ≠ q) :
    ∃ u v : Circle, ∃ l : ℝ, 0 < l ∧ l < 1 ∧ (v:ℂ) = -(u:ℂ) ∧
      (p:ℂ)*q = (u:ℂ)^2 ∧ (p:ℂ)+q = chord l (2*(u:ℂ)) (2*(v:ℂ)) := by
  let a := Complex.arg (p:ℂ)
  let b := Complex.arg (q:ℂ)
  let u := Circle.exp ((a+b)/2)
  let w := Circle.exp ((a-b)/2)
  have hp : u*w = p := by rw [← Circle.exp_add, show (a+b)/2 + (a-b)/2 = a by ring]; exact Circle.exp_arg _
  have hq : u*w⁻¹ = q := by rw [← Circle.exp_neg, ← Circle.exp_add, show (a+b)/2 + -((a-b)/2) = b by ring]; exact Circle.exp_arg _
  have hw : (w:ℂ).im ≠ 0 := by
    intro h
    have he : w = w⁻¹ := by
      apply Circle.ext
      rw [Circle.coe_inv_eq_conj]
      apply Complex.ext <;> simp [h]
    exact hpq (hp.symm.trans ((congrArg (fun v => u*v) he).trans hq))
  have hs := Complex.sq_norm_sub_sq_re (w:ℂ)
  rw [Circle.norm_coe] at hs
  have hr : -1 < (w:ℂ).re ∧ (w:ℂ).re < 1 := by
    constructor <;> nlinarith [sq_pos_of_ne_zero hw, sq_nonneg ((w:ℂ).re-1), sq_nonneg ((w:ℂ).re+1)]
  let v : Circle := ⟨-(u:ℂ), mem_sphere_zero_iff_norm.mpr (by simp [Circle.norm_coe])⟩
  refine ⟨u,v,(1-(w:ℂ).re)/2, by linarith [hr.2], by linarith [hr.1], rfl, ?_, ?_⟩
  · rw [← hp, ← hq, ← Circle.coe_mul]
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, Circle.coe_mul, pow_two]
  · rw [← hp, ← hq, Circle.coe_mul, Circle.coe_mul, Circle.coe_inv_eq_conj]
    have h : (w:ℂ) + conj (w:ℂ) = 2*((w:ℂ).re:ℂ) := by
      apply Complex.ext <;> simp
      ring
    change _ = chord _ (2*(u:ℂ)) (2*(-(u:ℂ)))
    rw [← mul_add, h]
    push_cast [chord]
    ring

theorem polarization_diagonal_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℕ → ℂ) (t : ℂ) :
    ∃ u : Circle, ∀ z : ι → Circle,
      ‖polarization univ c (fun i => (z i:ℂ)) - t‖ ≤
        ‖polarization (univ : Finset ι) c (fun _ => (u:ℂ)) - t‖ := by
  classical
  let F := fun z : ι → Circle => polarization univ c (fun i => (z i:ℂ)) - t
  let G := fun z : ι → Circle => ∑ i, (z i:ℂ)
  have hF : Continuous fun z => ‖F z‖^2 := by unfold F polarization; fun_prop
  have hG : Continuous fun z => ‖G z‖^2 := by unfold G; fun_prop
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hF.continuousOn
  let K := {z : ι → Circle | ‖F z‖^2 = ‖F m‖^2}
  have hK : IsCompact K := (isClosed_eq hF continuous_const).isCompact
  obtain ⟨z, hz, hGz⟩ := hK.exists_isMaxOn (show K.Nonempty from ⟨m,rfl⟩) hG.continuousOn
  have hf (y : ι → Circle) : ‖F y‖^2 ≤ ‖F z‖^2 := (hm (mem_univ y)).trans_eq hz.symm
  have hdiag (i j : ι) : z i = z j := by
    by_contra hpq
    have hij : i ≠ j := fun h => hpq (congrArg z h)
    obtain ⟨u,v,l,hl,hl',hv,hprod,hsum⟩ := pair_chord _ _ hpq
    obtain ⟨A,B,C,hsec⟩ := pair_section c z i j hij
    obtain ⟨T, htot⟩ := pair_sum z i j hij
    let U := replacePair z i j u u
    let V := replacePair z i j v v
    have hid : replacePair z i j (z i) (z j) = z := by simp [replacePair]
    have hFU : F U = A+B*((u:ℂ)+u)+C*(u:ℂ)*u-t := by dsimp [F,U]; rw [hsec]
    have hFV : F V = A+B*((v:ℂ)+v)+C*(v:ℂ)*v-t := by dsimp [F,V]; rw [hsec]
    have hFz : F z = chord l (F U) (F V) := by
      have hh := hsec (z i) (z j)
      rw [hid] at hh
      dsimp only [F] at hh ⊢
      change polarization _ _ _ - t = chord l (F U) (F V)
      rw [hh, hsum, mul_assoc C, hprod, hFU, hFV, hv]
      simp [chord]
      ring
    obtain ⟨huK,hvK⟩ := endpoints_eq hl hl' (congrArg (fun a : ℂ => ‖a‖^2) hFz) (hf U) (hf V)
    have huG := hGz (show U ∈ K from huK.trans hz)
    have hvG := hGz (show V ∈ K from hvK.trans hz)
    change ‖G U‖^2 ≤ ‖G z‖^2 at huG
    change ‖G V‖^2 ≤ ‖G z‖^2 at hvG
    have hGU : G U = T+u+u := htot u u
    have hGV : G V = T+v+v := htot v v
    have hGch : G z = chord l (G U) (G V) := by
      have hh := htot (z i) (z j)
      rw [hid, add_assoc, hsum] at hh
      change (∑ k, (z k:ℂ)) = _
      rw [hh, hGU, hGV]
      simp [chord]
      ring
    have hne : G U - G V ≠ 0 := by rw [hGU,hGV,hv]; intro h; apply u.coe_ne_zero; linear_combination h / 4
    have hstrict := mul_pos (mul_pos hl (sub_pos.mpr hl')) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))
    have H := congrArg (fun a : ℂ => ‖a‖^2) hGch
    change ‖G z‖^2 = ‖chord l (G U) (G V)‖^2 at H
    rw [chord_sq] at H
    have h1 := mul_le_mul_of_nonneg_left huG (sub_nonneg.mpr hl'.le)
    have h2 := mul_le_mul_of_nonneg_left hvG hl.le
    nlinarith only [H,hstrict,h1,h2]
  let i : ι := Classical.arbitrary ι
  refine ⟨z i, fun y => ?_⟩
  have heq : z = fun _ => z i := funext fun j => hdiag j i
  have H := hf y
  rw [heq] at H
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp H

theorem torusDisk_of_circle {n : ℕ} (hn : 0 < n)
    (h : ∀ u : Circle, ‖poly n (fun _ => (u:ℂ)) - (center n:ℂ)‖ ≤ radius n) :
    TorusDiskClaim n := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let c (k : ℕ) : ℂ := ((2/(2:ℝ)^n * Real.cos (((n:ℝ)-1)*Real.pi/4-(k:ℝ)*Real.pi/2):ℝ):ℂ)
  obtain ⟨u,hu⟩ := polarization_diagonal_max (ι := Fin n) c (center n:ℂ)
  intro z hz
  exact (hu (fun i => ⟨z i, mem_sphere_zero_iff_norm.mpr (hz i)⟩)).trans (h u)

end
end MABK
