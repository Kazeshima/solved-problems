import Quadric.Five.OneBlock
import Quadric.Five.Literals

namespace Quadric.Five.Census
deriving instance DecidableEq for Table
end Quadric.Five.Census

open Lean Elab Term
private def parseNat (s : String) : TermElabM Nat := do
  let some n := s.toNat? | throwError "invalid census integer"
  pure n

elab "tables% " s:str : term => do
  let mut tables : Array Expr := #[]
  for row in s.getString.splitOn ";" do
    let a::b::ns := row.splitOn "," | throwError "invalid lookup table"
    let offset ← parseNat a
    let width ← parseNat b
    let values ← ns.mapM parseNat
    let arr:=mkApp2 (mkConst ``List.toArray [.zero]) (mkConst ``Nat) (toExpr values)
    tables:=tables.push (mkAppN (mkConst ``Quadric.Five.Census.Table.mk) #[toExpr offset,toExpr width,arr])
  Meta.mkListLit (mkConst ``Quadric.Five.Census.Table) tables.toList

elab "blockRows% " s:str : term => do
  let mut rows : Array Expr := #[]
  for row in s.getString.splitOn "/" do
    let m::parts := row.splitOn "|" | throwError "invalid census row"
    let low ← parseNat m
    let mut slices : Array (Nat×List Nat) := #[]
    for part in parts do
      let a::bs:=part.splitOn "," | throwError "invalid census slice"
      let num ← parseNat a
      let answers ← bs.mapM parseNat
      slices:=slices.push (num,answers)
    rows:=rows.push (mkAppN (mkConst ``Quadric.Five.Census.Block.Row.mk) #[toExpr low,toExpr slices.toList])
  Meta.mkListLit (mkConst ``Quadric.Five.Census.Block.Row) rows.toList
