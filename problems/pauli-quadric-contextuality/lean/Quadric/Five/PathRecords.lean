import Quadric.Five.Paths
import Quadric.Five.Resources.MoveData
import Quadric.Five.Literals

namespace Quadric.Five.Moves
open Small Tagged
def hyperMask : ℕ := 0xf0f0f0f00f0f0f0e
theorem hyper_mask : hyperMask=packFlags (labels 3) (fun p=>sym 3 36 p==0) := by decide +kernel

structure Witness where
  start : ℕ
  target : ℕ
  word : List ℕ
  deriving Repr

def stable (m : Move) := (List.range 64).all (fun i=> !hyperMask.testBit i || hyperMask.testBit (source m i))
def stableBits : ℕ := 0xfff0f0f0f00f0f0f0f
def isStable (i : ℕ) := stableBits.testBit i
noncomputable def wordOK (onH : Bool) (w : Witness) :=
  let x:=walk Data.table w.word w.start
  if onH then (w.word.all isStable && (x &&& hyperMask)==w.target) else x==w.target

end Quadric.Five.Moves

open Lean Elab Term
elab "witnesses% " s:str : term => do
  let mut rows : Array Expr := #[]
  for l in s.getString.splitOn ";" do
    let a::b::ws:=l.splitOn "," | throwError "invalid orbit witness"
    let some x:=a.toNat? | throwError "invalid initial assignment"
    let some y:=b.toNat? | throwError "invalid target assignment"
    let mut word : Array Nat := #[]
    for v in ws do
      let some k:=v.toNat? | throwError "invalid generator"
      word:=word.push k
    rows:=rows.push (mkAppN (mkConst ``Quadric.Five.Moves.Witness.mk) #[toExpr x,toExpr y,toExpr word.toList])
  Meta.mkListLit (mkConst ``Quadric.Five.Moves.Witness) rows.toList

