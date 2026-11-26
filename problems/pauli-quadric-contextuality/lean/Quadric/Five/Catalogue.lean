import Quadric.Five.Tagged
import Quadric.Five.Literals

namespace Quadric.Five.Tagged
open Small

theorem in_whole {l : Line} (h : lineCheck true l=true) : lineCheck false l=true := by
  obtain ⟨a,b,c,d,e,f,g,v,sg,_⟩ := of_decide_eq_true h
  exact decide_eq_true ⟨a,b,c,d,e,f,g,v,sg,by simp⟩

theorem all_in_whole (ls : List Line) (h : ls.all (lineCheck true)=true) :
    ls.all (lineCheck false)=true :=
  List.all_eq_true.mpr fun l hl=>in_whole (List.all_eq_true.mp h l hl)

def advance : ℕ → List ℕ → Option ℕ
  | seen,[] => some seen
  | seen,k::ks => if seen.testBit k then none else advance (seen ||| (2^k)) ks

theorem advance_append (seen : ℕ) (xs ys : List ℕ) :
    advance seen (xs++ys)=(advance seen xs).bind (fun s=> advance s ys) := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,advance]; split <;> simp [ih]

theorem fresh_of_advance {seen result : ℕ} {xs : List ℕ} (h : advance seen xs=some result) :
    fresh seen xs=true := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    by_cases b : seen.testBit a=true
    · simp [advance,b] at h
    · simp only [advance,if_neg b] at h
      simp [fresh,b,ih h]

def Valid (b : Bool) (ls : List Line) := (ls.flatMap six).all (lineCheck b)=true
def Trace (ls : List Line) (x y : ℕ) := advance x ((ls.flatMap six).map key)=some y

theorem Valid.append {b : Bool} {l r : List Line} (h : Valid b l) (g : Valid b r) : Valid b (l++r) := by
  simpa only [Valid,List.flatMap_append,List.all_append,Bool.and_eq_true_iff] using And.intro h g

theorem Valid.weaken {ls : List Line} (h : Valid true ls) : Valid false ls := all_in_whole _ h

theorem Trace.append {l r : List Line} {x y z : ℕ} (h : Trace l x y) (g : Trace r y z) : Trace (l++r) x z := by
  unfold Trace at *
  rw [List.flatMap_append,List.map_append,advance_append,h]
  exact g

theorem Trace.unique {ls : List Line} {x y : ℕ} (h : Trace ls x y) :
    fresh x ((ls.flatMap six).map key)=true := fresh_of_advance h

end Quadric.Five.Tagged

open Lean Elab Term
elab "signedLines% " s:str : term => do
  let mut rows : Array Expr := #[]
  for row in s.getString.splitOn ";" do
    let [a,b,c,e] := row.splitOn "," | throwError "invalid signed line"
    let some p:=a.toNat? | throwError "invalid vertex"
    let some q:=b.toNat? | throwError "invalid vertex"
    let some t:=c.toNat? | throwError "invalid vertex"
    let some b:=e.toNat? | throwError "invalid phase"
    unless b<2 do throwError "invalid phase"
    rows:=rows.push (mkAppN (mkConst ``Quadric.Five.Small.Line.mk)
      #[toExpr p,toExpr q,toExpr t,toExpr (b==1)])
  Meta.mkListLit (mkConst ``Quadric.Five.Small.Line) rows.toList
