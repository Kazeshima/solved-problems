import Lean

/-! Data notation only. The macro emits ordinary constructor applications; subsequent proofs
use these values and the kernel checks their arithmetic and geometric properties. -/
open Lean Elab Term

elab "intRows% " s:str : term => do
  let mut rows : Array (List Int) := #[]
  for line in s.getString.splitOn ";" do
    if line.isEmpty then continue
    let mut row : Array Int := #[]
    for field in line.splitOn "," do
      let some x := field.trim.toInt? | throwError "invalid integer in certificate row"
      row := row.push x
    rows := rows.push row.toList
  return toExpr rows.toList

elab "natRows% " s:str : term => do
  let mut rows : Array (List Nat) := #[]
  for line in s.getString.splitOn ";" do
    let mut row : Array Nat := #[]
    for field in line.splitOn "," do
      if field.isEmpty then continue
      let some x := field.trim.toNat? | throwError "invalid natural in census row"
      row := row.push x
    rows := rows.push row.toList
  return toExpr rows.toList
