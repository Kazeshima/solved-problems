import Quadric.Five.Screen

namespace Quadric.Five.Census.Block
open Packing

abbrev Tables := List Table
def buildT (S : System) := S.groups.map (table S.lowWidth)
def vec (S : System) (T : Tables) (h : ℕ) := sumTables S.lowWidth T h (highCount S h)
theorem vec_spec (S : System) (h : ℕ) : vec S (buildT S) h=pack (2^S.lowWidth) (errorCount S h) :=
  table_sum_semantics .. 

def constantVector (k c : ℕ) : c*ones k=pack (2^k) (fun _=>c) := by
  rw [ones_eq,←pack_mul]; simp

structure Row where
  minB : ℕ
  slices : List (ℕ × List ℕ)
  deriving Repr

def member (r : Row) (a b : ℕ) := ∃ v∈r.slices,v.1=a ∧ b∈v.2

def prepared (S : Split) (tc : Tables) :=
  (S.first.lowWidth==10 && S.second.lowWidth==10 && S.crossBlock.lowWidth==10 &&
   S.lowFirst.length==1024 && S.cutoff<512 && S.high.length+size S.first+size S.second+size S.crossBlock≤511 &&
   S.lowFirst.all (·≤511)) &&
  (List.range 1024).all fun a=>packedLE 10 ((crossMinimumA S a)*ones 10) (vec S.crossBlock tc a)

def rowWithMinimum (S : Split) (ta tb tc : Tables) (minimum h : ℕ) (r : Row) :=
  let av:=vec S.first ta h
  let bv:=vec S.second tb h
  let hc:=highOnly S h
  let O:=ones 10
  r.minB≤511 && packedLE 10 (r.minB*O) bv &&
  winnersMask 10 S.cutoff (av+minimum+(hc+r.minB)*O)==declaredMask (r.slices.map Prod.fst) &&
  r.slices.all fun v=>winnersMask 10 S.cutoff
      (bv+vec S.crossBlock tc v.1+(hc+digit av v.1)*O)==declaredMask v.2

def rowOK (S : Split) (ta tb tc : Tables) (h : ℕ) (r : Row) :=
  rowWithMinimum S ta tb tc (packList S.lowFirst) h r

def cachedRun (S : Split) (ta tb tc : Tables) (minimum : ℕ) : ℕ → List Row → Bool
  | _,[]=>true
  | h,r::rs=>rowWithMinimum S ta tb tc minimum h r && cachedRun S ta tb tc minimum (h+1) rs

def run (S : Split) (ta tb tc : Tables) : ℕ → List Row → Bool
  | _,[]=>true
  | h,r::rs=>rowOK S ta tb tc h r && run S ta tb tc (h+1) rs

theorem cache_run (S : Split) (ta tb tc : Tables) (h : ℕ) (rs : List Row) :
    run S ta tb tc h rs=cachedRun S ta tb tc (packList S.lowFirst) h rs := by
  induction rs generalizing h with
  | nil => rfl
  | cons r rs ih => simp only [run,cachedRun,ih,rowOK]

theorem run_append (S : Split) (ta tb tc : Tables) (h : ℕ) (xs ys : List Row) :
    run S ta tb tc h (xs++ys)= (run S ta tb tc h xs && run S ta tb tc (h+xs.length) ys) := by
  induction xs generalizing h with
  | nil => simp [run]
  | cons x xs ih =>
    simp only [List.cons_append,run,List.length_cons,ih,Bool.and_assoc]
    congr 3 <;> omega

attribute [local irreducible] pack winnersMask declaredMask
private theorem mask_mem (k t : ℕ) (f : ℕ→ℕ) (hf : ∀ i<2^k,f i≤512) (ht : t<512)
    (xs : List ℕ) (eq : winnersMask k t (pack (2^k) f)=declaredMask xs) (i : ℕ) (hi : i<2^k) :
    f i≤t ↔ i∈xs := by
  have b:=congrArg (fun v:ℕ=>v.testBit (10*i+9)) eq
  have t:=(winner_bit k t f hf ht i hi).symm.trans (b.trans (declared_bit xs i))
  exact ⟨fun h=>of_decide_eq_true (t ▸ decide_eq_true h),fun h=>of_decide_eq_true (t.symm ▸ decide_eq_true h)⟩

theorem row_iff (S : Split) (h a b : ℕ) (ha : a<1024) (hb : b<1024) (r : Row)
    (ready : prepared S (buildT S.crossBlock)=true)
    (ok : rowOK S (buildT S.first) (buildT S.second) (buildT S.crossBlock) h r=true) :
    fullCost S h a b≤S.cutoff ↔ member r a b := by
  obtain ⟨shape,mn⟩:=Bool.and_eq_true_iff.mp ready
  simp only [Bool.and_eq_true_iff,beq_iff_eq,decide_eq_true_eq] at shape
  obtain ⟨⟨⟨⟨⟨⟨wa,wb⟩,wc⟩,len⟩,ht⟩,bud⟩,mlim⟩:=shape
  have subtotal (i j) : fullCost S h i j≤511 := by
    have h0 : highOnly S h≤S.high.length:=List.countP_le_length
    have := bounded S.first h i; have := bounded S.second h j; have := bounded S.crossBlock i j
    unfold fullCost; omega
  have cm (i j) (hi:i<1024) (hj:j<1024) : crossMinimumA S i≤errorCount S.crossBlock i j := by
    have z:=List.all_eq_true.mp mn i (List.mem_range.mpr hi)
    change packedLE 10 (crossMinimumA S i * ones 10) (vec S.crossBlock _ i)=true at z
    rw [constantVector,vec_spec,wc] at z
    have bound : crossMinimumA S i ≤ 511 := by
      unfold crossMinimumA
      have li : i<S.lowFirst.length := len.symm ▸ hi
      rw [List.getElem?_eq_getElem li,Option.getD_some]
      exact of_decide_eq_true (List.all_eq_true.mp mlim _ (List.getElem_mem li))
    exact packedLE_sound (fun _ _=>by omega) (fun q _=>by have := bounded S.crossBlock i q; omega) z hj
  simp only [rowOK,rowWithMinimum,Bool.and_eq_true_iff,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨lim,lo⟩,elig⟩,wins⟩:=ok
  rw [constantVector,vec_spec,wb] at lo
  have lb (j) (hj:j<1024) : r.minB≤errorCount S.second h j :=
    packedLE_sound (fun _ _=>by omega) (fun q _=>by have := bounded S.second h q; omega) lo hj
  let proj (i : ℕ) := errorCount S.first h i + crossMinimumA S i + (highOnly S h+r.minB)
  have le (i j) (hi:i<1024) (hj:j<1024) : proj i≤fullCost S h i j := by
    have := lb j hj; have := cm i j hi hj; dsimp [proj,fullCost]; omega
  rw [vec_spec,wa,packList_eq,len,constantVector,show (1024:ℕ)=2^10 by decide,←pack_add,←pack_add] at elig
  have eligible := mask_mem 10 S.cutoff proj (fun i hi=>by have := le i 0 hi (by decide); have := subtotal i 0; omega) ht _ elig a ha
  have slice (v : ℕ×List ℕ) (hv : v∈r.slices) (eq : v.1=a) :
      fullCost S h a b≤S.cutoff ↔ b∈v.2 := by
    have z:=eq_of_beq (List.all_eq_true.mp wins v hv)
    have d : digit (pack (2^10) (errorCount S.first h)) a=errorCount S.first h a :=
      digit_pack (2^10) (errorCount S.first h) (fun q _=>by have := bounded S.first h q; omega) a ha
    rw [eq,vec_spec,wb,vec_spec,wc,vec_spec,wa,d,
      constantVector,←pack_add,←pack_add] at z
    let f (j : ℕ) := errorCount S.second h j + errorCount S.crossBlock a j + (highOnly S h+errorCount S.first h a)
    have he (j) : f j=fullCost S h a j := by dsimp [f,fullCost]; omega
    simpa only [he] using mask_mem 10 S.cutoff f (fun j _=>(he j ▸ (subtotal a j)).trans (by decide)) ht _ z b hb
  constructor
  · intro hs
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp (eligible.mp ((le a b ha hb).trans hs))
    exact ⟨v,hv,eq,(slice v hv eq).mp hs⟩
  · rintro ⟨v,hv,eq,hw⟩; exact (slice v hv eq).mpr hw

theorem run_sound (S : Split) (ready : prepared S (buildT S.crossBlock)=true) (h : ℕ) (rs : List Row)
    (ok : run S (buildT S.first) (buildT S.second) (buildT S.crossBlock) h rs=true)
    (i a b : ℕ) (hi : i<rs.length) (ha : a<1024) (hb : b<1024) :
    fullCost S (h+i) a b≤S.cutoff ↔ member rs[i] a b := by
  induction rs generalizing h i with
  | nil => simp at hi
  | cons r rs ih =>
    obtain ⟨z,w⟩:=Bool.and_eq_true_iff.mp ok
    cases i with
    | zero => simpa using row_iff S h a b ha hb r ready z
    | succ i => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1) w i (by simpa using hi)

end Quadric.Five.Census.Block
