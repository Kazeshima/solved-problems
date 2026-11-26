import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Each base-1024 digit is one assignment in a low-dimensional Boolean cube. Only the tenth
bit is inspected after subtraction. The bound on the number of constraints prevents borrow
or carry between assignments. -/
namespace Quadric.Five.Packing

def pack : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => f 0+1024*pack n (fun i => f (i+1))

theorem pack_congr {n} {f g : ℕ→ℕ} (h : ∀ i<n, f i=g i) : pack n f=pack n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [pack,pack,h 0 (by omega),ih (fun i hi => h _ (by omega))]

theorem pack_add (n : ℕ) (f g : ℕ→ℕ) :
    pack n (fun i => f i+g i)=pack n f+pack n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [pack,ih]; ring

theorem pack_mul (n k : ℕ) (f : ℕ→ℕ) :
    pack n (fun i => k*f i)=k*pack n f := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih => simp only [pack,ih]; ring

theorem pack_zero (n : ℕ) : pack n (fun _ => 0)=0 := by
  induction n with | zero => rfl | succ n ih => simp [pack,ih]

theorem pack_split (m n : ℕ) (f : ℕ→ℕ) : pack (m+n) f =
    pack m f + 2^(10*m)*pack n (fun i => f (m+i)) := by
  induction m generalizing f with
  | zero => simp [pack]
  | succ m ih =>
    rw [Nat.succ_add,pack,ih,pack, Nat.mul_succ, pow_add]
    have hf : (fun i => f (m+i+1))=(fun i => f (m+1+i)) := by funext i; congr 1; omega
    rw [hf]; ring

def ones : ℕ → ℕ
  | 0 => 1
  | k+1 => let v := ones k; v + (v <<< (10*2^k))

theorem ones_eq (k : ℕ) : ones k=pack (2^k) (fun _ => 1) := by
  induction k with
  | zero => simp [ones,pack]
  | succ k ih =>
    rw [show 2^(k+1)=2^k+2^k by ring]
    rw [pack_split]; simp [ones,ih,Nat.shiftLeft_eq,mul_comm]

def parity : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => false
  | k+1,m,x => parity k m x ^^ (m.testBit k && x.testBit k)

theorem parity_congr {k m x y : ℕ} (h : ∀ j<k, x.testBit j=y.testBit j) :
    parity k m x=parity k m y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [parity,parity,ih (fun j hj => h j (by omega)),h k (by omega)]

def lowBits : ℕ → ℕ → Bool → ℕ
  | 0,_,b => b.toNat
  | k+1,m,b =>
    let v := lowBits k m b
    let w := if m.testBit k then ones k-v else v
    v + (w <<< (10*2^k))

theorem flipped (k : ℕ) (f : ℕ→Bool) :
    pack (2^k) (fun i => (!f i).toNat) = ones k-pack (2^k) (fun i => (f i).toNat) := by
  have h : pack (2^k) (fun i => (!f i).toNat)+pack (2^k) (fun i => (f i).toNat)=ones k := by
    rw [←pack_add,ones_eq]
    apply pack_congr; intro i _; cases f i <;> rfl
  omega

theorem lowBits_eq (k m : ℕ) (b : Bool) :
    lowBits k m b=pack (2^k) (fun x => (b ^^ parity k m x).toNat) := by
  induction k with
  | zero => cases b <;> rfl
  | succ k ih =>
    rw [show 2^(k+1)=2^k+2^k by ring,pack_split]
    have left : pack (2^k) (fun x => (b ^^ parity (k+1) m x).toNat) = lowBits k m b := by
      rw [ih]; apply pack_congr; intro i hi; simp [parity,Nat.testBit_lt_two_pow hi]
    have right : pack (2^k) (fun x => (b ^^ parity (k+1) m (2^k+x)).toNat) =
        if m.testBit k then ones k-lowBits k m b else lowBits k m b := by
      have hlo (x : ℕ) : parity k m (2^k+x)=parity k m x :=
        parity_congr fun j hj => Nat.testBit_two_pow_add_gt hj x
      by_cases hm : m.testBit k
      · rw [if_pos hm,ih,←flipped]
        apply pack_congr; intro x hx
        simp [parity,hlo,hm,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow hx]
      · rw [if_neg hm,ih]; apply pack_congr; intro x _
        simp [parity,hlo,hm]
    rw [left,right]; simp [lowBits,Nat.shiftLeft_eq,mul_comm]

theorem pack_bit (n : ℕ) (f : ℕ→ℕ) (hb : ∀ i<n, f i<1024) (x j : ℕ)
    (hx : x<n) (hj : j<10) : (pack n f).testBit (10*x+j)=(f x).testBit j := by
  induction n generalizing f x with
  | zero => omega
  | succ n ih =>
    rw [pack,Nat.add_comm (f 0)]
    have h0 : f 0<2^10 := hb _ (by omega)
    change (2^10 * pack n (fun i => f (i+1)) + f 0).testBit _ = _
    rw [Nat.testBit_two_pow_mul_add _ h0]
    cases x with
    | zero => simp [hj]
    | succ x =>
      have he : 10*(x+1)+j-10=10*x+j := by omega
      simp only [show ¬10*(x+1)+j<10 by omega,if_false,he]
      exact ih _ (fun i hi => hb _ (by omega)) x (by omega)

def winnersMask (k target sum : ℕ) : ℕ := ((512+target)*ones k-sum) &&& (512*ones k)

theorem winner_bit (k target : ℕ) (f : ℕ→ℕ) (hf : ∀ x<2^k, f x ≤ 512) (ht : target<512)
    (x : ℕ) (hx : x<2^k) :
    (winnersMask k target (pack (2^k) f)).testBit (10*x+9) = decide (f x ≤ target) := by
  have hplus : pack (2^k) (fun i => 512+target-f i)+pack (2^k) f=(512+target)*ones k := by
    rw [←pack_add,ones_eq,←pack_mul]
    apply pack_congr; intro i hi; have := hf _ hi; simp; omega
  have he : (512+target)*ones k-pack (2^k) f=pack (2^k) (fun i => 512+target-f i) := by omega
  rw [winnersMask,he,Nat.testBit_and,ones_eq,←pack_mul,pack_bit,pack_bit]
  · have hfx := hf x hx
    simp [Nat.testBit_to_div_mod]; omega
  all_goals first | assumption | omega | intro i hi; have := hf _ hi; omega

end Quadric.Five.Packing
