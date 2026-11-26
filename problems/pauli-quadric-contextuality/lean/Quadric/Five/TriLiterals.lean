import Quadric.Five.FastRows
import Quadric.Five.Literals
open Lean Elab Term

/-- Constructor notation for the submitted triangle multipliers. -/
elab "triangleRows% " s:str : term => do
  let mut rows : Array Expr := #[]
  for row in s.getString.splitOn ";" do
    let [a,b,c,u] := row.splitOn "," | throwError "invalid triangle"
    let some x := a.toNat? | throwError "invalid triangle vertex"
    let some y := b.toNat? | throwError "invalid triangle vertex"
    let some z := c.toNat? | throwError "invalid triangle vertex"
    let some w := u.toInt? | throwError "invalid triangle multiplier"
    rows := rows.push (mkAppN (mkConst ``Quadric.Five.Certificates.Triangle.mk)
      #[toExpr x,toExpr y,toExpr z,toExpr w])
  pure (← Meta.mkListLit (mkConst ``Quadric.Five.Certificates.Triangle) rows.toList)
