import Quadric.Five.Tagged
import Mathlib.Data.List.Sort

namespace Quadric.Five.Moves
open Tagged Small

structure Stage where
  stride : ℕ
  low : ℕ
  deriving DecidableEq,Repr

def swap (d : Stage) (x : ℕ) :=
  ((x >>> d.stride) &&& d.low) ||| ((x &&& d.low) <<< d.stride)
def back (d : Stage) (i : ℕ) := if d.low.testBit i then i+d.stride else i-d.stride
def stageOK (d : Stage) := (List.range 64).all fun i=>
  decide (back d i<64 ∧ (d.stride ≤ i ∧ d.low.testBit (i-d.stride) = true ↔ d.low.testBit i=false))

theorem swap_at (d : Stage) (x i : ℕ) (h : stageOK d=true) (hi : i<64) :
    (swap d x).testBit i=x.testBit (back d i) := by
  obtain ⟨_,ok⟩:=of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))
  simp only [swap,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_shiftLeft]
  cases hl : d.low.testBit i
  · obtain ⟨le,b⟩ := ok.mpr hl
    simp [back,hl,le,b]
  · have hn : ¬(d.stride ≤ i ∧ d.low.testBit (i-d.stride) = true) := by simp [ok,hl]
    by_cases hi' : d.stride ≤ i
    · have z : d.low.testBit (i-d.stride)=false := by cases e:d.low.testBit (i-d.stride) <;> simp_all
      simp [back,hi',hl,z,Nat.add_comm]
    · simp [back,hl,hi',Nat.add_comm]

def permute : List Stage → ℕ → ℕ
  | [],x=>x
  | d::ds,x=>swap d (permute ds x)
def route : List Stage → ℕ → ℕ
  | [],i=>i
  | d::ds,i=>route ds (back d i)

theorem permute_at (ds : List Stage) (x i : ℕ) (h : ds.all stageOK=true) (hi : i<64) :
    (permute ds x).testBit i=x.testBit (route ds i) ∧ route ds i<64 := by
  induction ds generalizing i with
  | nil => exact ⟨rfl,hi⟩
  | cons d ds ih =>
    obtain ⟨hd,hs⟩:=Bool.and_eq_true_iff.mp h
    have pos:=(of_decide_eq_true (List.all_eq_true.mp hd i (List.mem_range.mpr hi))).1
    simpa only [permute,route,swap_at d _ i hd hi] using ih _ hs pos

/-- The seven-bit lanes of image give the source tag for each destination. The entirety of the
point rephasing is in twist; the lower 64 positions are the three-qubit restriction. -/
structure Move where
  image : ℕ
  twist : ℕ
  active : ℕ
  stages : List Stage
  deriving Repr

def source (m : Move) (i : ℕ) := (m.image >>> (7*i))%128
def pull (m : Move) (s : ℕ→Bool) (i : ℕ) := s (source m i) ^^ m.twist.testBit i
def inner (m : Move) (x : ℕ) :=
  ((((permute m.stages x ^^^ x) &&& m.active) ^^^ x) ^^^ (m.twist%2^64))%2^64

def routeOK (m : Move) := m.stages.all stageOK && (List.range 64).all fun i =>
  source m i == if m.active.testBit i then route m.stages i else i

theorem inner_at (m : Move) (s : ℕ→Bool) (hm : routeOK m=true) (i : ℕ) (hi:i<64) :
    (inner m (carrier s)).testBit i = pull m s i := by
  obtain ⟨shape,src⟩:=Bool.and_eq_true_iff.mp hm
  have eq:=eq_of_beq (List.all_eq_true.mp src i (List.mem_range.mpr hi))
  have hh:=permute_at m.stages (carrier s) i shape hi
  simp only [inner,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and,Nat.testBit_xor,
    Nat.testBit_and,hh.1,carrier_at s _ hh.2,carrier_at s _ hi,pull,eq]
  cases b:m.active.testBit i <;> simp [b]

theorem inner_carrier (m : Move) (s : ℕ→Bool) (hm : routeOK m=true) :
    inner m (carrier s)=carrier (pull m s) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi:i<64
  · rw [inner_at _ _ hm _ hi,carrier_at _ _ hi]
  · unfold inner; rw [Nat.testBit_mod_two_pow]; simp [hi,carrier,flag_bit]

def ordered (a b c : ℕ) (n : Bool) : Line :=
  if a≤b then if b≤c then ⟨a,b,c,n⟩ else if a≤c then ⟨a,c,b,n⟩ else ⟨c,a,b,n⟩
  else if a≤c then ⟨b,a,c,n⟩ else if b≤c then ⟨b,c,a,n⟩ else ⟨c,b,a,n⟩

theorem fail_ordered (s : ℕ→Bool) (a b c : ℕ) (n : Bool) :
    Small.failure s (ordered a b c n)=(s a ^^ s b ^^ s c ^^ n) := by
  unfold ordered; split_ifs <;> simp only [Small.failure,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

def relabel (m : Move) (l : Line) := ordered (source m l.a) (source m l.b) (source m l.c)
  (m.twist.testBit l.a ^^ m.twist.testBit l.b ^^ m.twist.testBit l.c ^^ l.neg)

theorem failure_pull (m : Move) (s : ℕ→Bool) (l : Line) :
    Small.failure (pull m s) l=Small.failure s (relabel m l) := by
  rw [relabel,fail_ordered]
  simp only [Small.failure,pull,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

theorem preserves (m : Move) {ls : List Line} (h : (ls.map (relabel m)).Perm ls) (s : ℕ→Bool) :
    errors ls (pull m s)=errors ls s := by
  have eq:=h.countP_eq (Small.failure s)
  simpa only [errors,List.countP_map,Function.comp_def,←failure_pull] using eq

def code (l : Line) := ((l.a*128+l.b)*128+l.c)*2+l.neg.toNat
def arranged (ls : List Line) := ls.mergeSort fun a b=>code a ≤ code b
def lineOK (m : Move) (ls : List Line) := decide (arranged (ls.map (relabel m))=arranged ls)

theorem line_perm {m : Move} {ls : List Line} (h : lineOK m ls=true) : (ls.map (relabel m)).Perm ls := by
  have eq:=of_decide_eq_true h
  have lhs : (ls.map (relabel m)).Perm (arranged (ls.map (relabel m))) := (List.mergeSort_perm ..).symm
  rw [eq] at lhs
  exact lhs.trans (List.mergeSort_perm ..)

end Quadric.Five.Moves
