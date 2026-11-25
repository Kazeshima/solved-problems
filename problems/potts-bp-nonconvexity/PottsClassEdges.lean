import PottsClassColumn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace PottsBP.Classification
open Finset Set
open scoped BigOperators
noncomputable section

def Bounds (d : ℕ) (β : ℝ) (x : Fin 3 → ℝ) : Prop :=
  (∀ a b, β^d*x b ≤ x a) ∧ ∀ (a b c : Fin 3) (m n : ℕ), a≠b → m+n+1=d →
    (1+β)*x c ≤ x a/β^m+x b/β^n

lemma bounds_scale {d : ℕ} {β s : ℝ} {x : Fin 3 → ℝ} (hs : 0 ≤ s) (h : Bounds d β x) :
    Bounds d β (fun i => s*x i) := by
  constructor
  · intro a b; calc
      _ = s*(β^d*x b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h.1 a b) hs
  · intro a b c m n hab hd
    calc
      _ = s*((1+β)*x c) := by ring
      _ ≤ s*(x a/β^m+x b/β^n) := mul_le_mul_of_nonneg_left (h.2 a b c m n hab hd) hs
      _ = _ := by ring

lemma bounds_add {d : ℕ} {β : ℝ} {x y : Fin 3 → ℝ} (h : Bounds d β x) (k : Bounds d β y) :
    Bounds d β (x+y) := by
  constructor
  · intro a b; simp only [Pi.add_apply,mul_add]; exact add_le_add (h.1 a b) (k.1 a b)
  · intro a b c m n hab hd
    simp only [Pi.add_apply,mul_add,add_div]
    linarith only [h.2 a b c m n hab hd,k.2 a b c m n hab hd]

lemma raw_bounds {d : ℕ} {β : ℝ} (hb : 0<β) (h1 : β<1) (p : Fin d → Fin 3 → ℝ)
    (hp : ∀ j,simplexN (p j)) : Bounds d β (rawWeight β p) := by
  constructor
  · intro a b
    have ha : β^d ≤ rawWeight β p a := by
      have h := Finset.prod_le_prod (s:=univ) (f:=fun _ : Fin d => β)
        (g:=fun j => 1-(1-β)*p j a) (fun _ _ => hb.le) (fun j _ => by
          change β ≤ 1-(1-β)*p j a
          nlinarith only [mul_nonneg (sub_nonneg.mpr h1.le) (sub_nonneg.mpr (simplexN_le_one (hp j) a))])
      simpa [rawWeight] using h
    exact (mul_le_of_le_one_right (pow_nonneg hb.le _) (raw_le_one hp hb.le h1.le b)).trans ha
  · intro a b c m n hab hd
    have col (i : Fin 3) (k : ℕ) : 1+(1-β)*((k:ℝ)-∑ j,p j i) ≤ rawWeight β p i/β^k := by
      apply (le_div_iff₀ (pow_pos hb k)).2
      rw [mul_comm]
      exact column_tangent univ _ hb.le h1.le (fun j => (hp j).1 i) (fun j => simplexN_le_one (hp j) i) k
    have rows (j : Fin d) : p j a + p j b ≤ 1 := by
      have hh := sum_le_sum_of_subset_of_nonneg (s:={a,b}) (t:=univ) (subset_univ _)
        (fun i _ _ => (hp j).1 i)
      rwa [sum_pair hab,(hp j).2] at hh
    have sm : (∑ j,p j a)+(∑ j,p j b) ≤ (d:ℝ) := by
      rw [← sum_add_distrib]
      simpa using sum_le_sum (s:=univ) (fun j _ => rows j)
    have hc := mul_le_of_le_one_right (show 0≤1+β by linarith) (raw_le_one hp hb.le h1.le c)
    have hcast : (m:ℝ)+n+1=d := by exact_mod_cast hd
    have hmul := mul_nonneg (sub_nonneg.mpr h1.le) (sub_nonneg.mpr sm)
    rw [← hcast] at hmul
    nlinarith only [hc,hmul,col a m,col b n]

lemma bounds_of_mem {d : ℕ} {β : ℝ} (hb : 0<β) (h1 : β<1) {x : Fin 3 → ℝ}
    (hx : x∈generalImage 3 d β) : Bounds d β x := by
  obtain ⟨p,hp,hZ,rfl⟩ := hx
  change Bounds d β (fun i => rawWeight β p i / (∑ k,rawWeight β p k))
  simpa only [generalBP,div_eq_inv_mul] using
    bounds_scale (inv_nonneg.mpr hZ.le) (raw_bounds hb h1 p hp)

def edgeWeight (β : ℝ) (a b : Fin 3) (m n : ℕ) (s : ℝ) (i : Fin 3) :=
  pinFactor β a i ^ m * pinFactor β b i ^ n * ((1-s)*pinFactor β a i+s*pinFactor β b i)

lemma edge_realizes {β s : ℝ} (a b : Fin 3) (m n : ℕ) (hs : s∈Icc (0:ℝ) 1) :
    Realizes 3 (m+n+1) β (edgeWeight β a b m n s) := by
  let v (a : Fin 3) (i : Fin 3) : ℝ := if a=i then 1 else 0
  have r : Realizes 3 m β (fun i => pinFactor β a i ^ m) := by
    simpa using add_pins (realizes_empty 3 β) a m
  have h := prepend (add_pins r b n) ((1-s) • v a+s • v b)
    ((convex_stdSimplex ℝ (Fin 3)) (singleton_pin a) (singleton_pin b) (sub_nonneg.mpr hs.2) hs.1 (by ring))
  convert h using 1
  funext i
  by_cases ha : a=i <;> by_cases hb : b=i <;> simp [edgeWeight,pinFactor,ha,hb,v] <;> ring

lemma edge_equality {β : ℝ} (hb : 0<β) {a b c : Fin 3} (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (m n : ℕ) (s : ℝ) :
    let g := edgeWeight β a b m n s
    (1+β)*g c = g a / β^m + g b / β^n := by
  simp [edgeWeight,pinFactor,hab,hac,hbc,Ne.symm hab,ne_of_gt hb]
  ring

private lemma crosses (f : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) (h0 : f 0 ≤ 0) (h1 : 0 ≤ f d) :
    ∃ k, k<d ∧ f k ≤ 0 ∧ 0 ≤ f (k+1) := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases h : f d ≤ 0
    · exact ⟨d,by omega,h,h1⟩
    · have hn : d≠0 := by
        intro hd0
        apply h
        simpa [hd0] using h0
      have hd' : 1 ≤ d := by omega
      obtain ⟨k,hk,hk0,hk1⟩ := ih hd' (le_of_not_ge h)
      exact ⟨k,by omega,hk0,hk1⟩

theorem edge_cross {d : ℕ} (hd : 1≤d) (β R : ℝ) (a b : Fin 3)
    (h0 : pinFactor β a 0 ^ d ≤ R*pinFactor β a 1 ^ d)
    (h1 : R*pinFactor β b 1 ^ d ≤ pinFactor β b 0 ^ d) :
    ∃ (m n : ℕ) (s : ℝ) (p : Fin d → Fin 3 → ℝ), m+n+1=d ∧ (∀ j,simplexN (p j)) ∧
      rawWeight β p = edgeWeight β a b m n s ∧ rawWeight β p 0 = R*rawWeight β p 1 := by
  let V (k : ℕ) (i : Fin 3) := pinFactor β a i ^ (d-k) * pinFactor β b i ^ k
  let h (k : ℕ) := V k 0 - R*V k 1
  obtain ⟨k,hk,hlo,hhi⟩ := crosses h hd
    (by simpa [h,V] using sub_nonpos.mpr h0) (by simpa [h,V] using sub_nonneg.mpr h1)
  let m := d-(k+1)
  have hmk : m+k+1=d := by dsimp [m]; omega
  let G (s : ℝ) := edgeWeight β a b m k s
  let L (s : ℝ) := G s 0 - R*G s 1
  have e0 (i) : G 0 i=V k i := by
    have hm : d-k=m+1 := by dsimp [m]; omega
    simp [G,V,edgeWeight,hm,pow_succ]; ring
  have e1 (i) : G 1 i=V (k+1) i := by
    simp [G,V,edgeWeight,m,pow_succ]; ring
  have cont : Continuous L := by dsimp [L,G,edgeWeight]; fun_prop
  have l0 : L 0 ≤ 0 := by simpa only [L,e0,h] using hlo
  have l1 : 0 ≤ L 1 := by simpa only [L,e1,h] using hhi
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) cont.continuousOn
    (show 0∈Icc (L 0) (L 1) from ⟨l0,l1⟩)
  have real : Realizes 3 d β (G s) := hmk ▸ edge_realizes (β:=β) a b m k hs
  obtain ⟨p,hp,eq⟩ := real
  exact ⟨m,k,s,p,hmk,hp,eq,by rw [eq]; exact sub_eq_zero.mp he⟩

end
end PottsBP.Classification
