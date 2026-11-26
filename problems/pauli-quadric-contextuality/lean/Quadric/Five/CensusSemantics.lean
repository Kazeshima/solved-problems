import Quadric.Five.CensusEval
import Quadric.Five.Tagged
import Mathlib.Data.List.Sort

namespace Quadric.Five.Census
open Packing Small

/-- A parity constraint, in free-coordinate order. -/
structure Affine where
  vars : List ℕ
  neg : Bool
  deriving DecidableEq, Repr

def foldBits (s : ℕ→Bool) : List ℕ→Bool
  | []=>false
  | i::is=>s i ^^ foldBits s is

theorem fold_append (s : ℕ→Bool) (xs ys : List ℕ) :
    foldBits s (xs++ys) = (foldBits s xs ^^ foldBits s ys) := by
  induction xs with | nil => simp [foldBits] | cons x xs ih => simp [foldBits,ih,Bool.xor_assoc]

theorem fold_perm (s : ℕ→Bool) {xs ys : List ℕ} (h : xs.Perm ys) :
    foldBits s xs=foldBits s ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [foldBits,ih]
  | swap a b l => simp [foldBits,Bool.xor_left_comm]
  | trans _ _ h1 h2 => exact h1.trans h2

def normalized (f : Affine) : Affine := ⟨f.vars.insertionSort (·≤·),f.neg⟩
def eval (s : ℕ→Bool) (f : Affine) := foldBits s f.vars ^^ f.neg

@[simp] theorem eval_normal (s : ℕ→Bool) (f : Affine) : eval s (normalized f)=eval s f := by
  unfold eval normalized; rw [fold_perm s (List.perm_insertionSort ..)]

def field (s : ℕ→Bool) (off width : ℕ) :=
  Tagged.packFlags (List.range width) fun i=>s (off+i)

theorem field_at (s : ℕ→Bool) (off width i : ℕ) :
    (field s off width).testBit i=(decide (i<width) && s (off+i)) := by simp [field,Tagged.flag_bit]

private theorem field_lt_aux (keys : List ℕ) (b : ℕ) (f : ℕ→Bool) (H : ∀i∈keys,i<b) :
    Tagged.packFlags keys f < 2^b := by
  induction keys with
  | nil => exact Nat.two_pow_pos b
  | cons k ks ih =>
    have h := ih (fun i hi=>H i (List.mem_cons_of_mem _ hi))
    change (if f k then (2^k)|||Tagged.packFlags ks f else Tagged.packFlags ks f)<2^b
    split
    · exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) (H k (by simp))) h
    · exact h

theorem field_lt (s : ℕ→Bool) (off width : ℕ) : field s off width<2^width :=
  field_lt_aux _ _ _ (fun _ hi=>List.mem_range.mp hi)

def shifted (off width : ℕ) (xs : List ℕ) := (xs.filter (·<width)).map (off+·)

theorem shifted_field (s : ℕ→Bool) (off width : ℕ) (xs : List ℕ) :
    foldBits s (shifted off width xs) = highBit xs (field s off width) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h:x<width <;> simp [shifted,List.filter_cons,h,foldBits,highBit,field_at,←ih]

theorem shifted_sub (g : Group) (h : ℕ) (xs : List ℕ) :
    highBit (shifted g.offset g.width xs) h=highBit xs (subkey g h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases he : x<g.width <;> simp [shifted,List.filter_cons,he,highBit,subkey,Nat.testBit_mod_two_pow,←ih] <;> exact ih

def support : ℕ→ℕ→List ℕ
  | 0,_=>[]
  | k+1,m=>if m.testBit k then k::support k m else support k m

theorem support_eval (k m l : ℕ) : highBit (support k m) l=parity k m l := by
  induction k with
  | zero => rfl
  | succ k ih => cases z:m.testBit k <;> simp [support,parity,highBit,ih,z,Bool.xor_comm]

def rawForms (S : System) (lo hi : ℕ) : List Affine :=
  (S.highForms.map fun u=>⟨shifted hi S.highWidth u.1,u.2⟩) ++
  S.groups.flatMap fun g => g.forms.map fun t=>
    ⟨shifted hi S.highWidth (shifted g.offset g.width t.highVars) ++ shifted lo S.lowWidth (support S.lowWidth t.lowMask),t.flip⟩

theorem system_geometry (S : System) (s : ℕ→Bool) (lo hi : ℕ) :
    (rawForms S lo hi).countP (eval s)=errorCount S (field s hi S.highWidth) (field s lo S.lowWidth) := by
  simp only [rawForms,List.countP_append,List.countP_map,List.countP_flatMap,List.map_map,
    errorCount,highCount,groupErrors,Function.comp_def]
  congr 1
  · apply List.countP_congr
    intro q _; simp [eval,shifted_field]
  · congr 1
    apply List.map_congr_left; intro g hg
    try simp only [List.countP_map,Function.comp_def]
    apply List.countP_congr; intro t _
    simp only [eval,fold_append,shifted_field,shifted_sub,support_eval,lowError]
    simp [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

def pointForm (free : List ℕ) (rep p : ℕ) : Affine :=
  if p∈free then ⟨[free.idxOf p],false⟩ else ⟨[],rep.testBit p⟩
def extendBits (free : List ℕ) (rep : ℕ) (s : ℕ→Bool) (p : ℕ) := eval s (pointForm free rep p)

def lineForm (free : List ℕ) (rep : ℕ) (l : Line) : Affine :=
  let a:=pointForm free rep l.a
  let b:=pointForm free rep l.b
  let c:=pointForm free rep l.c
  ⟨a.vars++b.vars++c.vars,a.neg ^^ b.neg ^^ c.neg ^^ l.neg⟩

theorem eval_line (s : ℕ→Bool) (free : List ℕ) (rep : ℕ) (l : Line) :
    eval s (lineForm free rep l)=Small.failure (extendBits free rep s) l := by
  dsimp only [lineForm,eval,Small.failure,extendBits]
  rw [fold_append,fold_append]
  simp only [Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem compare_system (S : System) (lo hi : ℕ) (ls : List Line) (free : List ℕ) (rep : ℕ)
    (eq : ((rawForms S lo hi).map normalized).Perm ((ls.map (lineForm free rep)).map normalized))
    (s : ℕ→Bool) : errorCount S (field s hi S.highWidth) (field s lo S.lowWidth)=
      errors ls (extendBits free rep s) := by
  rw [←system_geometry]
  have h:=eq.countP_eq (p:=eval s)
  simpa only [List.countP_map,Function.comp_def,eval_normal,eval_line,errors] using h

end Quadric.Five.Census
