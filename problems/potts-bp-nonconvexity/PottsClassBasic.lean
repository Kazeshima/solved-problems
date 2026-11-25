import PottsBPGeneral
import Mathlib.Algebra.BigOperators.Field

namespace PottsBP
open Finset Set
open scoped BigOperators
noncomputable section

/-- Equations (1) and (2), restricted to the domain of positive normalization. -/
def admissibleSourceImage (q d : ℕ) (β : ℝ) : Set (Fin q → ℝ) :=
  {x | ∃ p : Fin d → Fin q → ℝ, (∀ j, simplexN (p j)) ∧
    (0 < ∑ i, sourceWeight β (productLaw p) i) ∧ sourceBP β (productLaw p) = x}

theorem admissibleSourceImage_eq_generalImage {q d : ℕ} (β : ℝ) :
    admissibleSourceImage q d β = generalImage q d β := by
  ext x
  constructor <;> rintro ⟨p,hp,hZ,hx⟩
  · exact ⟨p,hp,by simpa only [sourceWeight_eq_rawWeight β p hp] using hZ,
      (sourceBP_eq_generalBP β p hp).symm.trans hx⟩
  · exact ⟨p,hp,by simpa only [sourceWeight_eq_rawWeight β p hp] using hZ,
      (sourceBP_eq_generalBP β p hp).trans hx⟩

namespace Classification
variable {q d : ℕ} {β : ℝ}

def total (g : Fin q → ℝ) : ℝ := ∑ i, g i
def normVec (g : Fin q → ℝ) (i : Fin q) := g i / total g

def Realizes (q d : ℕ) (β : ℝ) (g : Fin q → ℝ) : Prop :=
  ∃ p : Fin d → Fin q → ℝ, (∀ j, simplexN (p j)) ∧ rawWeight β p = g

lemma Realizes.mem {g : Fin q → ℝ} (hg : Realizes q d β g) (hZ : 0 < total g) :
    normVec g ∈ generalImage q d β := by
  obtain ⟨p,hp,h⟩ := hg
  refine ⟨p,hp,?_,?_⟩
  · simpa only [h] using (show 0 < ∑ i, g i from hZ)
  · funext i; simp only [generalBP,normVec,total,h]

lemma factor_pos {p : Fin d → Fin q → ℝ} (hp : ∀ j, simplexN (p j))
    (hb : 0 < β) (h1 : β ≤ 1) (j : Fin d) (i : Fin q) :
    0 < 1-(1-β)*p j i := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (simplexN_le_one (hp j) i))]

lemma raw_pos {p : Fin d → Fin q → ℝ} (hp : ∀ j, simplexN (p j))
    (hb : 0 < β) (h1 : β ≤ 1) (i : Fin q) : 0 < rawWeight β p i :=
  Finset.prod_pos fun j _ => factor_pos hp hb h1 j i

lemma raw_nonneg {p : Fin d → Fin q → ℝ} (hp : ∀ j, simplexN (p j))
    (hb : 0 ≤ β) (h1 : β ≤ 1) (i : Fin q) : 0 ≤ rawWeight β p i :=
  Finset.prod_nonneg fun j _ => sub_nonneg.mpr (scaled_entry_bounds hb h1 hp j i).2

lemma raw_le_one {p : Fin d → Fin q → ℝ} (hp : ∀ j, simplexN (p j))
    (hb : 0 ≤ β) (h1 : β ≤ 1) (i : Fin q) : rawWeight β p i ≤ 1 :=
  Finset.prod_le_one (fun j _ => sub_nonneg.mpr (scaled_entry_bounds hb h1 hp j i).2)
    (fun j _ => sub_le_self _ (scaled_entry_bounds hb h1 hp j i).1)

lemma total_pos_of_pos [NeZero q] {g : Fin q → ℝ} (hg : ∀ i, 0 < g i) : 0 < total g :=
  Finset.sum_pos (fun i _ => hg i) Finset.univ_nonempty

lemma general_subset_simplex (hb : 0 ≤ β) (h1 : β ≤ 1) :
    generalImage q d β ⊆ stdSimplex ℝ (Fin q) := by
  rintro _ ⟨p,hp,hZ,rfl⟩
  exact ⟨fun i => div_nonneg (raw_nonneg hp hb h1 i) hZ.le,by
    simp only [generalBP, ← Finset.sum_div, div_self hZ.ne']⟩

lemma singleton_pin (a : Fin q) : simplexN (fun i => if a=i then (1:ℝ) else 0) := by
  constructor
  · intro i; change 0 ≤ (if a=i then (1:ℝ) else 0); split <;> norm_num
  · simp

def pinFactor (β : ℝ) (a i : Fin q) : ℝ := if a=i then β else 1

lemma prepend {g : Fin q → ℝ} (hg : Realizes q d β g) (v : Fin q → ℝ) (hv : simplexN v) :
    Realizes q (d+1) β (fun i => (1-(1-β)*v i)*g i) := by
  obtain ⟨p,hp,rfl⟩ := hg
  refine ⟨Fin.cons v p,Fin.forall_fin_succ.mpr ⟨hv,hp⟩,?_⟩
  funext i
  simp [rawWeight,Fin.prod_univ_succ]

lemma add_pins {g : Fin q → ℝ} (hg : Realizes q d β g) (a : Fin q) (m : ℕ) :
    Realizes q (d+m) β (fun i => (pinFactor β a i)^m * g i) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    have hh := prepend ih _ (singleton_pin a)
    have eqf : (fun i => (1-(1-β)*(if a=i then (1:ℝ) else 0))*(pinFactor β a i ^ m * g i)) =
        (fun i => pinFactor β a i ^ (m+1) * g i) := by
      funext i
      by_cases hi : a=i <;> simp [pinFactor,hi,pow_succ,mul_assoc,mul_comm,mul_left_comm]
    rw [eqf] at hh
    exact hh

lemma realizes_empty (q : ℕ) (β : ℝ) : Realizes q 0 β (fun _ => 1) := by
  exact ⟨fun j => Fin.elim0 j,fun j => Fin.elim0 j,by ext; simp [rawWeight]⟩

lemma uniform_simplex [NeZero q] : simplexN (fun _ : Fin q => (1:ℝ)/q) :=
  ⟨fun _ => by positivity, by simp [ne_of_gt (Nat.cast_pos.mpr (NeZero.pos q) : (0:ℝ)<q)]⟩

lemma general_mono_degree (hq : 2 ≤ q) (hb : 0 ≤ β) {e : ℕ} (hde : d ≤ e) :
    generalImage q d β ⊆ generalImage q e β := by
  letI : NeZero q := ⟨by omega⟩
  induction e, hde using Nat.le_induction with
  | base => exact fun _ h => h
  | succ n hn ih =>
    intro x hx
    obtain ⟨p,hp,hZ,rfl⟩ := ih hx
    let a := 1-(1-β)*((1:ℝ)/q)
    have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
    have ha : 0 < a := by dsimp [a]; field_simp; nlinarith
    have h := prepend (show Realizes q n β (rawWeight β p) from ⟨p,hp,rfl⟩) _ uniform_simplex
    have hS : (∑ i, a*rawWeight β p i) = a*(∑ i,rawWeight β p i) := (mul_sum ..).symm
    have hr := h.mem (show 0 < total (fun i => a*rawWeight β p i) by
      unfold total; rw [hS]; exact mul_pos ha hZ)
    convert hr using 1
    funext i
    change rawWeight β p i / _ = (a * rawWeight β p i) / ∑ k, a*rawWeight β p k
    rw [hS]; field_simp; ring

lemma legacy_eq_of_pos (h : ∀ p : Fin d → Fin q → ℝ, (∀ j, simplexN (p j)) →
    0 < ∑ i, rawWeight β p i) : sourceImage q d β = admissibleSourceImage q d β := by
  rw [admissibleSourceImage_eq_generalImage]
  ext x
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,h p hp,(sourceBP_eq_generalBP β p hp).symm.trans hx⟩
  · rintro ⟨p,hp,_,hx⟩
    exact ⟨p,hp,(sourceBP_eq_generalBP β p hp).trans hx⟩

end Classification

open Classification

theorem source_convex_beta_one (q d : ℕ) : Convex ℝ (admissibleSourceImage q d 1) := by
  rw [admissibleSourceImage_eq_generalImage]
  intro x hx y hy a b ha hb hab
  obtain ⟨p,hp,hz,rfl⟩ := hx
  obtain ⟨r,hr,_,rfl⟩ := hy
  refine ⟨p,hp,hz,?_⟩
  funext i
  simp [generalBP,rawWeight,Pi.add_apply,Pi.smul_apply,← add_mul,hab]

theorem source_convex_one_neighbor {q : ℕ} (hq : 2 ≤ q) {β : ℝ} (h0 : 0 ≤ β) :
    Convex ℝ (admissibleSourceImage q 1 β) := by
  rw [admissibleSourceImage_eq_generalImage]
  have sum1 (p : Fin 1 → Fin q → ℝ) (hp : ∀ j, simplexN (p j)) :
      (∑ i,rawWeight β p i) = (q:ℝ)-(1-β) := by
    simp [rawWeight,Fin.prod_univ_succ,sum_sub_distrib,← mul_sum,(hp 0).2]
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  intro x hx y hy a b ha hb hab
  obtain ⟨p,hp,_,rfl⟩ := hx
  obtain ⟨r,hr,_,rfl⟩ := hy
  let s (j : Fin 1) := a • p j + b • r j
  have hs (j) : simplexN (s j) := (convex_stdSimplex ℝ (Fin q)) (hp j) (hr j) ha hb hab
  refine ⟨s,hs,by rw [sum1 s hs]; linarith,?_⟩
  funext i
  simp only [generalBP,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum1 s hs,sum1 p hp,sum1 r hr]
  simp [rawWeight,Fin.prod_univ_succ,s]
  rw [← mul_div_assoc,← mul_div_assoc,← add_div]
  congr 1
  linear_combination -hab

end
end PottsBP
