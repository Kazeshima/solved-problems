import Quadric.Five.Moves

namespace Quadric.Five.Moves
open Small Tagged

structure Good (m : Move) : Prop where
  routing : routeOK m=true
  inside : (full3.map (relabel m)).Perm full3
  outside : (outsideLines.map (relabel m)).Perm outsideLines

theorem Good.elliptic {m : Move} (hm : Good m) (s : ℕ→Bool) :
    errors ellipticLines (pull m s)=errors ellipticLines s := by
  apply preserves
  simpa only [ellipticLines,List.map_append] using hm.inside.append hm.outside

def walk (table : List Move) : List ℕ→ℕ→ℕ
  | [],x=>x
  | i::is,x=>walk table is (match table[i]? with | some m=>inner m x | none=>x)

def action (table : List Move) : List ℕ→(ℕ→Bool)→(ℕ→Bool)
  | [],s=>s
  | i::is,s=>action table is (match table[i]? with | some m=>pull m s | none=>s)

theorem travel (table : List Move) (ht : ∀ m∈table,Good m) (w : List ℕ) (s : ℕ→Bool) :
    carrier (action table w s)=walk table w (carrier s) ∧
    errors full3 (action table w s)=errors full3 s ∧
    errors ellipticLines (action table w s)=errors ellipticLines s := by
  induction w generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons i is ih =>
    cases he:table[i]? with
    | none => simpa only [action,walk,he] using ih s
    | some m =>
      have good:=ht m (List.mem_of_getElem? he)
      obtain ⟨hw,hi,ha⟩:=ih (pull m s)
      simp only [action,walk,he]
      exact ⟨hw.trans (congrArg (walk table is) (inner_carrier m s good.routing).symm),
        hi.trans (preserves m good.inside s),ha.trans (good.elliptic s)⟩

def keyBits (x : ℕ) : List ℕ→ℕ
  | []=>0
  | p::ps=>(x.testBit p).toNat+2*keyBits x ps

def gaugeWord (choices : List (List ℕ)) (frame : List ℕ) (x : ℕ) : List ℕ :=
  choices[keyBits x frame]?.getD []

def normal (table : List Move) (choices : List (List ℕ)) (frame : List ℕ) (x : ℕ) :=
  walk table (gaugeWord choices frame x) x

end Quadric.Five.Moves
