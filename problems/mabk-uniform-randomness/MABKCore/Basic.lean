import Mathlib

/-!
# MABK with uniform outputs (Wooltorton--Brown--Colbeck, Conjecture 1)

Definitions and certificates from the submitted draft. The two disk predicates
below express mathematical statements. Defining them supplies no proofs.
-/

open scoped BigOperators
open Set

namespace MABK

noncomputable section

/-- Strict convexity of squared Euclidean norm along a nontrivial chord. -/
theorem chord_identity (a b c d l : ℝ) :
    ((1-l)*a+l*c)^2 + ((1-l)*b+l*d)^2 =
    (1-l)*(a^2+b^2) + l*(c^2+d^2) -
      l*(1-l)*((a-c)^2+(b-d)^2) := by
  ring

theorem chord_endpoint_improves (a b c d l : ℝ)
    (hl : 0 < l) (hl' : l < 1) (hne : a ≠ c ∨ b ≠ d) :
    ((1-l)*a+l*c)^2 + ((1-l)*b+l*d)^2 <
      max (a^2+b^2) (c^2+d^2) := by
  have hp : 0 < (a-c)^2+(b-d)^2 := by
    rcases hne with h | h
    · have hh : a-c ≠ 0 := sub_ne_zero.mpr h
      have hsq : 0 < (a-c)^2 := sq_pos_of_ne_zero hh
      nlinarith [sq_nonneg (b-d)]
    · have hh : b-d ≠ 0 := sub_ne_zero.mpr h
      have hsq : 0 < (b-d)^2 := sq_pos_of_ne_zero hh
      nlinarith [sq_nonneg (a-c)]
  have hgap : 0 < l*(1-l)*((a-c)^2+(b-d)^2) :=
    mul_pos (mul_pos hl (sub_pos.mpr hl')) hp
  have h1 := mul_le_mul_of_nonneg_left
    (le_max_left (a^2+b^2) (c^2+d^2)) (sub_nonneg.mpr hl'.le)
  have h2 := mul_le_mul_of_nonneg_left
    (le_max_right (a^2+b^2) (c^2+d^2)) hl.le
  rw [chord_identity]
  nlinarith

/-- A finite arithmetic certificate used outside the central interval.
    k = n * δ²; r bounds the modulus of the curve there. -/
theorem outer_gap (δ k t m r : ℝ) (hδ : 0 < δ)
    (hk : (3/5 : ℝ)*δ ≤ k)
    (ht : t ≤ (101/100 : ℝ)*δ)
    (hm : 1-(41/100 : ℝ)*δ ≤ m)
    (hr : r ≤ 1-(13/4 : ℝ)*k+(3/8 : ℝ)*δ) :
    r+t < m := by
  linarith

/-- The sign factor of the derivative of squared distance.
    In the application f(y)=sin(y)cos(y)^n-ε cos(y)sin(y)^n,
    g has the opposite sign ε, and S(x)=sin(π/4+(n+1)x). -/
def signFactor (f g S : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if x < 0 then g (-x) + t*S x else -f x + t*S x

/-- All hypotheses here are elementary interval estimates, proved
    analytically in the accompanying mathematical proof. -/
theorem signFactor_left (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t)
    (htU : t ≤ (101/100 : ℝ)*δ)
    (f g S : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ x → x ≤ δ →
      f x ≤ t-(3/4 : ℝ)*(δ-x))
    (hg0 : ∀ y, 0 ≤ y → y ≤ δ → 0 ≤ g y)
    (hg1 : ∀ y, δ ≤ y → y ≤ 2*δ → (3/4 : ℝ)*t ≤ g y)
    (hg2 : ∀ y, 2*δ ≤ y → y ≤ 3*δ → t ≤ g y)
    (hs0 : ∀ x, -δ ≤ x → x ≤ 0 → 0 ≤ S x)
    (hs1 : ∀ x, -2*δ ≤ x → x ≤ -δ → -(3/4 : ℝ) ≤ S x)
    (hs2 : ∀ x, -3*δ ≤ x → x ≤ -2*δ → -1 ≤ S x)
    (hs3 : ∀ x, 0 ≤ x → x ≤ δ →
      1-(δ-x)/(2*δ) ≤ S x) :
    ∀ x, -3*δ ≤ x → x ≤ δ → 0 ≤ signFactor f g S t x := by
  intro x hxL hxU
  by_cases hx : x < 0
  · rw [signFactor, if_pos hx]
    by_cases hy : -x ≤ δ
    · exact add_nonneg (hg0 (-x) (by linarith) hy)
        (mul_nonneg ht (hs0 x (by linarith) hx.le))
    · by_cases hy' : -x ≤ 2*δ
      · have hG := hg1 (-x) (by linarith) hy'
        have hS := mul_le_mul_of_nonneg_left
          (hs1 x (by linarith) (by linarith)) ht
        linarith
      · have hG := hg2 (-x) (by linarith) (by linarith)
        have hS := mul_le_mul_of_nonneg_left
          (hs2 x hxL (by linarith)) ht
        linarith
  · rw [signFactor, if_neg hx]
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have hdiv : t/(2*δ) ≤ (3/4 : ℝ) := by
      apply (div_le_iff₀ (show 0 < 2*δ by positivity)).2
      linarith
    have hM := mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hxU)
    have hS := mul_le_mul_of_nonneg_left (hs3 x hx0 hxU) ht
    have heq : t*(1-(δ-x)/(2*δ)) = t-(t/(2*δ))*(δ-x) := by ring
    rw [heq] at hS
    linarith [hf x hx0 hxU]

theorem signFactor_right (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t)
    (f g S : ℝ → ℝ)
    (hf : ∀ x, δ ≤ x → x ≤ 3*δ → t ≤ f x)
    (hs : ∀ x, δ ≤ x → x ≤ 3*δ → S x ≤ 1) :
    ∀ x, δ ≤ x → x ≤ 3*δ → signFactor f g S t x ≤ 0 := by
  intro x hxL hxU
  have hx : ¬ x < 0 := by linarith
  rw [signFactor, if_neg hx]
  have h := mul_le_mul_of_nonneg_left (hs x hxL hxU) ht
  linarith [hf x hxL hxU]

/-- Calculus certificate: the interval derivative signs and the outer bound
    suffice for the global maximum of squared distance. -/
theorem global_disk_certificate (D K H : ℝ → ℝ) (δ R m : ℝ)
    (hδ : 0 < δ) (hD : Differentiable ℝ D)
    (hval : D δ = m^2)
    (hderiv : ∀ x, deriv D x = K x * H x)
    (hK : ∀ x, -3*δ ≤ x → x ≤ 3*δ → 0 ≤ K x)
    (hL : ∀ x, -3*δ ≤ x → x ≤ δ → 0 ≤ H x)
    (hR : ∀ x, δ ≤ x → x ≤ 3*δ → H x ≤ 0)
    (hout : ∀ x ∈ Icc (-R) R,
      x < -3*δ ∨ 3*δ < x → D x ≤ m^2) :
    ∀ x ∈ Icc (-R) R, D x ≤ m^2 := by
  have hmono : MonotoneOn D (Icc (-3*δ) δ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      hD.continuous.continuousOn hD.differentiableOn
    intro x hx
    have hx' : x ∈ Icc (-3*δ) δ := interior_subset hx
    rw [hderiv]
    exact mul_nonneg (hK x hx'.1 (by linarith [hx'.2]))
      (hL x hx'.1 hx'.2)
  have hanti : AntitoneOn D (Icc δ (3*δ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      hD.continuous.continuousOn hD.differentiableOn
    intro x hx
    have hx' : x ∈ Icc δ (3*δ) := interior_subset hx
    rw [hderiv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hK x (by linarith [hx'.1]) hx'.2) (hR x hx'.1 hx'.2)
  intro x hx
  by_cases hxl : x < -3*δ
  · exact hout x hx (Or.inl hxl)
  by_cases hxr : 3*δ < x
  · exact hout x hx (Or.inr hxr)
  by_cases hmid : x ≤ δ
  · have hh := hmono (show x ∈ Icc (-3*δ) δ from ⟨le_of_not_gt hxl,hmid⟩)
      (show δ ∈ Icc (-3*δ) δ from ⟨by linarith,le_rfl⟩) hmid
    exact hh.trans_eq hval
  · have hh := hanti (show δ ∈ Icc δ (3*δ) from ⟨le_rfl,by linarith⟩)
      (show x ∈ Icc δ (3*δ) from ⟨le_of_not_ge hmid,le_of_not_gt hxr⟩)
      (le_of_not_ge hmid)
    exact hh.trans_eq hval

/-- Exact normalized MABK polynomial, divided by 2^((n-1)/2). -/
def poly (n : ℕ) (z : Fin n → ℂ) : ℂ :=
  Finset.sum (Finset.univ : Finset (Fin n)).powerset (fun s =>
    ((2 / (2:ℝ)^n * Real.cos (((n:ℝ)-1)*Real.pi/4 -
        (s.card:ℝ)*Real.pi/2) : ℝ) : ℂ) * Finset.prod s z)

def δ (n : ℕ) : ℝ := Real.pi/(4*((n:ℝ)+1))
def ε (n : ℕ) : ℝ := if n % 4 = 2 then 1 else -1

def radius (n : ℕ) : ℝ :=
  Real.cos (δ n)^(n+1) + ε n * Real.sin (δ n)^(n+1)

def center (n : ℕ) : ℝ :=
  (if n % 8 = 0 ∨ n % 8 = 2 then 1 else -1) *
    (Real.sin (δ n) * Real.cos (δ n)^n -
      ε n * Real.cos (δ n) * Real.sin (δ n)^n)

/-- The precise torus disk theorem from the mathematical proof.
    A proposition, NOT an asserted theorem or a new axiom. -/
def TorusDiskClaim (n : ℕ) : Prop :=
  ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) →
    ‖poly n z - (center n : ℂ)‖ ≤ radius n

/-- Explicit normalized diagonal curve in real coordinates. -/
def diagonalRe (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (Real.pi/4+(n:ℝ)*x) * Real.cos x^n -
    ε n * Real.sin (Real.pi/4+(n:ℝ)*x) * Real.sin x^n

def diagonalIm (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (Real.pi/4+(n:ℝ)*x) * Real.cos x^n +
    ε n * Real.cos (Real.pi/4+(n:ℝ)*x) * Real.sin x^n

def canonicalCenter (n : ℕ) : ℝ :=
  Real.sin (δ n)*Real.cos (δ n)^n -
    ε n*Real.cos (δ n)*Real.sin (δ n)^n

def DiagonalDiskClaim (n : ℕ) : Prop :=
  ∀ x ∈ Icc (-(Real.pi/4)) (Real.pi/4),
    (diagonalRe n x - canonicalCenter n)^2 + (diagonalIm n x)^2 ≤ (radius n)^2

/-- Linear certificate for mixing strategies, including cancellation of E(0). -/
theorem weighted_bound {k : ℕ} (w a b : Fin k → ℝ) (t m : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hzero : ∑ i, w i * b i = 0)
    (hpoint : ∀ i, a i - t*b i ≤ m) :
    ∑ i, w i * a i ≤ m := by
  have h : (∑ i, w i*(a i-t*b i)) ≤ ∑ i, w i*m := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i))
  have heq : (∑ i, w i*(a i-t*b i)) =
      (∑ i, w i*a i) - t*(∑ i, w i*b i) := by
    calc
      _ = ∑ i, (w i*a i-t*(w i*b i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq, hzero, mul_zero, sub_zero, ← Finset.sum_mul, hsum, one_mul] at h
  exact h

/-- Assuming the explicit torus disk claim, all finite convex combinations of
    GHZ full-correlator strategies satisfy the desired normalized upper bound.
    The identification of arbitrary quantum full correlators with this convex
    hull (or the equivalent operator norm proof) is not formalized in this file. -/
theorem finite_phase_mixture_bound {n k : ℕ} (hdisk : TorusDiskClaim n)
    (w : Fin k → ℝ) (u : Fin k → ℂ) (z : Fin k → Fin n → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, ‖u i‖ = 1) (hz : ∀ i j, ‖z i j‖ = 1)
    (hzero : ∑ i, w i * (u i).re = 0) :
    ∑ i, w i * (u i * poly n (z i)).re ≤ radius n := by
  apply weighted_bound w (fun i => (u i * poly n (z i)).re)
    (fun i => (u i).re) (center n) (radius n) hw hsum hzero
  intro i
  have h : (u i * (poly n (z i) - (center n : ℂ))).re ≤ radius n := by
    calc
      _ ≤ ‖u i * (poly n (z i) - (center n : ℂ))‖ := Complex.re_le_norm _
      _ = ‖poly n (z i) - (center n : ℂ)‖ := by rw [norm_mul, hu i, one_mul]
      _ ≤ _ := hdisk (z i) (hz i)
  have heq : (u i * (poly n (z i) - (center n : ℂ))).re =
      (u i * poly n (z i)).re - center n * (u i).re := by
    rw [mul_sub, Complex.sub_re, Complex.mul_re (u i) (center n : ℂ)]
    simp
    ring
  rw [heq] at h
  exact h

end
end MABK
