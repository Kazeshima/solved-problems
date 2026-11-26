import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Fraction-free symmetric elimination. Store the diagonal followed by the upper
entries in each row. The certificate is valid only if every division is exact and
every pivot is positive. The soundness proof works for every integer vector. -/
namespace Quadric.Five.Schur

abbrev Rows := List (List ℤ)

def dot : List ℤ → List ℤ → ℤ
  | a::as',x::xs => a*x+dot as' xs
  | _,_ => 0

def quad : Rows → List ℤ → ℤ
  | (p::v)::a,x::xs => p*x^2+2*x*dot v xs+quad a xs
  | _,_ => 0

def row (d p b : ℤ) : List ℤ → List ℤ → List ℤ
  | c::cs,a::as' => (p*a-b*c)/d :: row d p b cs as'
  | _,_ => []

def rowOK (d p b : ℤ) : List ℤ → List ℤ → Bool
  | [],[] => true
  | c::cs,a::as' =>
      (d*((p*a-b*c)/d) == p*a-b*c) && rowOK d p b cs as'
  | _,_ => false

def next (d p : ℤ) : List ℤ → Rows → Rows
  | b::bs,r::rs => row d p b (b::bs) r :: next d p bs rs
  | _,_ => []

def stepOK (d p : ℤ) : List ℤ → Rows → Bool
  | [],[] => true
  | b::bs,(a::as')::rs => rowOK d p b (b::bs) (a::as') && stepOK d p bs rs
  | _,_ => false

def check : ℕ → ℤ → Rows → Bool
  | 0,_,rs => rs.isEmpty
  | n+1,d,(p::v)::rs => (0 < p) && stepOK d p v rs && check n p (next d p v rs)
  | _+1,_,_ => false

theorem dot_row (d p b : ℤ) (v r xs : List ℤ) (h : rowOK d p b v r = true) :
    d * dot (row d p b v r) xs = p * dot r xs - b * dot v xs := by
  induction v generalizing r xs with
  | nil =>
    cases r <;> simp_all [rowOK,row,dot]
  | cons c cs ih =>
    cases r with
    | nil => simp [rowOK] at h
    | cons a as' =>
      obtain ⟨he,hr⟩ := Bool.and_eq_true_iff.mp h
      have hv : d*((p*a-b*c)/d)=p*a-b*c := of_decide_eq_true (by simpa using he)
      cases xs with
      | nil => simp [dot,row]
      | cons x xs =>
        simp only [row,dot]
        linear_combination x*hv + ih as' xs hr

theorem next_quad (d p : ℤ) (v : List ℤ) (a : Rows) (xs : List ℤ)
    (h : stepOK d p v a = true) :
    d*quad (next d p v a) xs = p*quad a xs - (dot v xs)^2 := by
  induction v generalizing a xs with
  | nil =>
    cases a <;> simp_all [stepOK,next,quad,dot]
  | cons b bs ih =>
    cases a with
    | nil => simp [stepOK] at h
    | cons r rs =>
      cases r with
      | nil => simp [stepOK] at h
      | cons k ks =>
        obtain ⟨hrow,hrest⟩ := Bool.and_eq_true_iff.mp h
        obtain ⟨hdiag,htail⟩ := Bool.and_eq_true_iff.mp hrow
        have hd : d*((p*k-b*b)/d)=p*k-b*b := by simpa using hdiag
        cases xs with
        | nil => simp [next,row,quad,dot]
        | cons x xs =>
          simp only [next,row,quad,dot]
          linear_combination x^2*hd + (2*x)*dot_row d p b bs ks xs htail + ih rs xs hrest

theorem sound (n : ℕ) (d : ℤ) (a : Rows) (hd : 0<d) (h : check n d a=true)
    (xs : List ℤ) : 0 ≤ quad a xs := by
  induction n generalizing d a xs with
  | zero => cases a <;> simp_all [check,quad]
  | succ n ih =>
    cases a with
    | nil => simp [check] at h
    | cons r rs =>
      cases r with
      | nil => simp [check] at h
      | cons p v =>
        obtain ⟨hpv,hn⟩ := Bool.and_eq_true_iff.mp h
        obtain ⟨hpp,hs⟩ := Bool.and_eq_true_iff.mp hpv
        have hp : 0<p := of_decide_eq_true hpp
        cases xs with
        | nil => simp [quad]
        | cons x xs =>
          have he := next_quad d p v rs xs hs
          have identity : p*quad ((p::v)::rs) (x::xs) =
              (p*x+dot v xs)^2 + d*quad (next d p v rs) xs := by
            simp only [quad]; linear_combination -he
          apply nonneg_of_mul_nonneg_right (a:=p) _ hp
          rw [identity]
          exact add_nonneg (sq_nonneg _) (mul_nonneg hd.le (ih p _ hp hn xs))

end Quadric.Five.Schur
