import Quadric.Five.Packing

namespace Quadric.Five.Census
open Packing

structure Term where
  lowMask : ℕ
  highVars : List ℕ
  flip : Bool
  deriving Repr
structure Group where
  offset : ℕ
  width : ℕ
  forms : List Term
  deriving Repr
structure System where
  lowWidth : ℕ
  highWidth : ℕ
  threshold : ℕ
  highForms : List (List ℕ × Bool)
  groups : List Group
  deriving Repr

def highBit : List ℕ → ℕ → Bool
  | [],_ => false
  | j::js,x => x.testBit j ^^ highBit js x

def subkey (g : Group) (h : ℕ) := (h >>> g.offset) % (2^g.width)
def highCount (S : System) (h : ℕ) :=
  S.highForms.countP fun a => highBit a.1 h ^^ a.2
def lowError (k l : ℕ) (t : Term) (h : ℕ) :=
  (highBit t.highVars h ^^ t.flip) ^^ parity k t.lowMask l

def groupErrors (k h l : ℕ) (g : Group) :=
  g.forms.countP fun t => lowError k l t (subkey g h)
def errorCount (S : System) (h l : ℕ) :=
  highCount S h + (S.groups.map (groupErrors S.lowWidth h l)).sum

def groupValue (k j : ℕ) (g : Group) :=
  (g.forms.map fun t => lowBits k t.lowMask (highBit t.highVars j ^^ t.flip)).sum

structure Table where
  offset : ℕ
  width : ℕ
  data : Array ℕ

def table (k : ℕ) (g : Group) : Table :=
  ⟨g.offset,g.width,((List.range (2^g.width)).map fun j => groupValue k j g).toArray⟩

def valueAt (t : Table) (h : ℕ) :=
  t.data[(h >>> t.offset) % (2^t.width)]?.getD 0

def sumTables (k : ℕ) (T : List Table) (h v : ℕ) :=
  v*ones k+(T.map fun t => valueAt t h).sum

def declaredMask (ls : List ℕ) : ℕ :=
  ls.foldr (fun i acc => (1 <<< (10*i+9)) ||| acc) 0

/-- Each row contains the exact list of the low-coordinate survivors for one high coordinate. -/
def pass (S : System) (tables : List Table) (h : ℕ) (ls : List ℕ) : Bool :=
  winnersMask S.lowWidth S.threshold (sumTables S.lowWidth tables h (highCount S h)) == declaredMask ls

def checkRows (S : System) (tables : List Table) : ℕ → List (List ℕ) → Bool
  | _,[] => true
  | h,x::xs => pass S tables h x && checkRows S tables (h+1) xs

def rowsOK (S : System) (start : ℕ) (xs : List (List ℕ)) :=
  checkRows S (S.groups.map (table S.lowWidth)) start xs

theorem table_at (k : ℕ) (g : Group) (h : ℕ) :
    valueAt (table k g) h=groupValue k (subkey g h) g := by
  have ht : (h >>> g.offset) % 2^g.width < 2^g.width := Nat.mod_lt _ (by positivity)
  simp [valueAt,table,subkey,List.getElem?_map,ht]

private theorem pack_counts {α : Type*} (xs : List α) (f : α → ℕ → Bool) (n : ℕ) :
    (xs.map fun a => pack n (fun i => (f a i).toNat)).sum =
    pack n (fun i => xs.countP (fun a => f a i)) := by
  induction xs with
  | nil => simp [pack_zero]
  | cons a as ih =>
    rw [List.map_cons,List.sum_cons,ih,←pack_add]
    apply pack_congr
    intro i hi
    cases h : f a i <;> simp [List.countP_cons,h,Nat.add_comm]

theorem group_semantics (k h : ℕ) (g : Group) :
    valueAt (table k g) h = pack (2^k) (fun l => groupErrors k h l g) := by
  rw [table_at,groupValue]
  simp_rw [lowBits_eq]
  exact pack_counts g.forms (fun t l => lowError k l t (subkey g h)) _

private theorem pack_sums {α : Type*} (gs : List α) (f : α → ℕ → ℕ) (n : ℕ) :
    (gs.map fun g => pack n (f g)).sum = pack n (fun x => (gs.map (fun g => f g x)).sum) := by
  induction gs with
  | nil => simp [pack_zero]
  | cons g gs ih => simp only [List.map_cons,List.sum_cons,ih,pack_add]

theorem table_sum_semantics (S : System) (h : ℕ) :
    sumTables S.lowWidth (S.groups.map (table S.lowWidth)) h (highCount S h) =
      pack (2^S.lowWidth) (errorCount S h) := by
  rw [sumTables,ones_eq,←pack_mul,List.map_map]
  change _ + (S.groups.map (fun g => valueAt (table S.lowWidth g) h)).sum = _
  simp_rw [group_semantics,pack_sums,←pack_add]
  apply pack_congr; intro i hi; simp [errorCount]

theorem declared_bit (xs : List ℕ) (x : ℕ) :
    (declaredMask xs).testBit (10*x+9) = decide (x∈xs) := by
  induction xs with
  | nil => simp [declaredMask]
  | cons i is ih =>
    change ((1 <<< (10*i+9)) ||| declaredMask is).testBit (10*x+9) = _
    rw [Nat.testBit_or,ih,Nat.shiftLeft_eq]
    simp [Nat.testBit_two_pow,eq_comm, List.mem_cons, Bool.decide_or]

def size (S : System) := S.highForms.length + (S.groups.map (fun g => g.forms.length)).sum

theorem bounded (S : System) (h l : ℕ) : errorCount S h l ≤ size S := by
  unfold errorCount size
  apply Nat.add_le_add List.countP_le_length
  generalize S.groups=gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add List.countP_le_length ih

theorem row_sound (S : System) (hc : size S ≤ 512) (ht : S.threshold < 512)
    (h l : ℕ) (hl : l<2^S.lowWidth) (xs : List ℕ)
    (ok : pass S (S.groups.map (table S.lowWidth)) h xs = true) :
    errorCount S h l ≤ S.threshold ↔ l ∈ xs := by
  have he := congrArg (fun a : ℕ => a.testBit (10*l+9)) (eq_of_beq ok)
  change (winnersMask S.lowWidth S.threshold _).testBit _ = (declaredMask xs).testBit _ at he
  rw [table_sum_semantics,winner_bit _ _ _ (fun i _ => (bounded S h i).trans hc) ht l hl,
    declared_bit] at he
  constructor
  · intro h; exact of_decide_eq_true (he ▸ decide_eq_true h)
  · intro h; exact of_decide_eq_true (he.symm ▸ decide_eq_true h)

theorem rows_sound (S : System) (hc : size S≤512) (ht : S.threshold<512)
    (start : ℕ) (rows : List (List ℕ)) (ok : rowsOK S start rows=true)
    (j l : ℕ) (hj : j<rows.length) (hl : l<2^S.lowWidth) :
    errorCount S (start+j) l≤S.threshold ↔ l∈rows[j] := by
  induction rows generalizing start j with
  | nil => simp at hj
  | cons x xs ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp ok
    cases j with
    | zero => simpa using row_sound S hc ht start l hl x ha
    | succ j =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) hb j (by simpa using hj)

end Quadric.Five.Census
