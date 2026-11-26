import Quadric.Five.CensusEval

namespace Quadric.Five.Census
open Packing

def digit (v i : ℕ) := (v >>> (10*i))%1024

theorem digit_pack (n : ℕ) (f : ℕ→ℕ) (hb : ∀i<n,f i<1024) (i : ℕ) (hi : i<n) :
    digit (pack n f) i=f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    have h0:=hb 0 (by omega)
    cases i with
    | zero => simp [digit,pack,Nat.add_mod,Nat.mod_eq_of_lt h0]
    | succ i =>
      have hstep : (pack (n+1) f >>> 10)=pack n (fun j=>f (j+1)) := by
        rw [pack,Nat.shiftRight_eq_div_pow]
        change (f 0+1024*pack n (fun j=>f (j+1)))/1024=_
        rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h0, Nat.zero_add]
      unfold digit; rw [show 10*(i+1)=10+10*i by omega, Nat.shiftRight_add,hstep]
      exact ih _ (fun j hj=>hb _ (by omega)) i (by omega)

def packList : List ℕ → ℕ
  | [] => 0
  | x::xs => x+(packList xs <<< 10)
theorem packList_eq (xs : List ℕ) :
    packList xs=pack xs.length (fun i=>xs[i]?.getD 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [packList,pack,ih,Nat.shiftLeft_eq,mul_comm]

def packedLE (k x y : ℕ) := (((512*ones k+y-x) &&& (512*ones k)) == 512*ones k)

theorem packedLE_sound {k : ℕ} {f g : ℕ→ℕ} (hf : ∀ i<2^k,f i≤512)
    (hg : ∀ i<2^k,g i<512)
    (h : packedLE k (pack (2^k) f) (pack (2^k) g)=true) {i : ℕ} (hi : i<2^k) :
    f i ≤ g i := by
  have hadd : pack (2^k) (fun j=>512+g j-f j)+pack (2^k) f =
       512*ones k + pack (2^k) g := by
    rw [←pack_add,ones_eq,←pack_mul,←pack_add]
    apply pack_congr; intro j hj; have := hf _ hj; simp; omega
  have hsub : 512*ones k+pack (2^k) g-pack (2^k) f=pack (2^k) (fun j=>512+g j-f j) := by omega
  have b := congrArg (fun v : ℕ=>v.testBit (10*i+9)) (eq_of_beq h)
  change (((512*ones k+pack (2^k) g-pack (2^k) f) &&& (512*ones k)).testBit _)=
    (512*ones k).testBit _ at b
  have z : (512*ones k).testBit (10*i+9)=true := by
    rw [ones_eq,←pack_mul,pack_bit _ _ (by intros; norm_num) _ _ hi (by decide : 9<10)]; decide
  have hd (j) (hj:j<2^k) : 512+g j-f j<1024 := by have := hg _ hj; omega
  rw [Nat.testBit_and,z,Bool.and_true,hsub,pack_bit _ _ hd _ _ hi (by decide : 9<10)] at b
  by_contra hn
  have hlt : 512+g i-f i < 2^9 := by change _ < 512; omega
  rw [Nat.testBit_lt_two_pow hlt] at b; contradiction

/-- Bits 0..7 are a, 8..15 are b, and the remaining bits are h. Each edge potential is
allocated to exactly one of the four summands. -/
structure Split where
  first : System
  second : System
  crossBlock : System
  high : List (List ℕ × Bool)
  cutoff : ℕ
  lowFirst : List ℕ
  lowSecond : List ℕ
  deriving Repr

def highOnly (S : Split) (h : ℕ) := S.high.countP fun t=>highBit t.1 h ^^ t.2
def fullCost (S : Split) (h a b : ℕ) :=
  highOnly S h + errorCount S.first h a + errorCount S.second h b + errorCount S.crossBlock a b
def vector (s : System) (h : ℕ) := sumTables s.lowWidth (s.groups.map (table s.lowWidth)) h (highCount s h)
theorem vector_eq (s : System) (h : ℕ) : vector s h=pack (2^s.lowWidth) (errorCount s h) :=
  table_sum_semantics _ _

structure Row where
  minA : ℕ
  minB : ℕ
  candA : List ℕ
  candB : List ℕ
  hits : List ℕ
  deriving Repr

def crossMinimumA (S : Split) (a : ℕ) := S.lowFirst[a]?.getD 0
def crossMinimumB (S : Split) (b : ℕ) := S.lowSecond[b]?.getD 0

def prepOK (S : Split) : Bool :=
  (S.first.lowWidth==8 && S.second.lowWidth==8 && S.crossBlock.lowWidth==8 &&
   S.lowFirst.length==256 && S.lowSecond.length==256 && S.cutoff<512 &&
   S.high.length+size S.first+size S.second+size S.crossBlock≤511 &&
   S.lowFirst.all (·≤511) && S.lowSecond.all (·≤511)) &&
  (List.range 256).all fun a =>
    let crossV:=vector S.crossBlock a
    packedLE 8 (crossMinimumA S a * ones 8) crossV &&
    packedLE 8 (packList S.lowSecond) crossV

def rowPass (S : Split) (h : ℕ) (r : Row) : Bool :=
  let av:=vector S.first h
  let bv:=vector S.second h
  let hc:=highOnly S h
  let O:=ones 8
  r.minA≤511 && r.minB≤511 &&
  packedLE 8 (r.minA*O) av && packedLE 8 (r.minB*O) bv &&
  winnersMask 8 S.cutoff (av+packList S.lowFirst+(hc+r.minB)*O)==declaredMask r.candA &&
  winnersMask 8 S.cutoff (bv+packList S.lowSecond+(hc+r.minA)*O)==declaredMask r.candB &&
  r.candA.all (fun a=> r.candB.all (fun b=>
      let v := hc+digit av a+digit bv b+digit (vector S.crossBlock a) b
      decide (S.cutoff<v) || r.hits.contains (a+256*b))) &&
  r.hits.all (fun ab=> ab<65536 && hc+digit av (ab%256)+digit bv (ab/256)+
    digit (vector S.crossBlock (ab%256)) (ab/256)≤S.cutoff)

def rowChecks (S : Split) : ℕ → List Row → Bool
  | _,[] => true
  | h,r::rs => rowPass S h r && rowChecks S (h+1) rs

end Quadric.Five.Census
