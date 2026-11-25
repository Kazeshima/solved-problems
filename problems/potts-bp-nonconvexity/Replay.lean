import PottsBPGeneral
import Lean.Replay

/-! Independent kernel replay of the cited proof terms above the pinned Lean Init library.
This file is a verifier. The mathematical modules do not import it. -/
open Lean

private def replayTargets : List Name :=
  [``PottsBP.question4_false, ``PottsBP.source_question4_false,
   ``PottsBP.source_nonconvex_general, ``PottsBP.productLaw_isProbability,
   ``PottsBP.sourceImage_eq_generalImage, ``PottsBP.sourceWeight_eq_rawWeight]

run_cmd
  let src ← getEnv
  let base ← importModules #[{module := `Init}] {} 0
  let mut pending := replayTargets
  let mut additions : Std.HashMap Name ConstantInfo := {}
  repeat
    let n :: tail := pending | break
    pending := tail
    if base.contains n || additions.contains n then continue
    let some ci := src.find? n | throwError "Missing declaration {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Non-kernel dependency {n}"
    if ci matches .axiomInfo _ then throwError "Axiom outside Init: {n}"
    additions := additions.insert n ci
    pending := ci.getUsedConstantsAsSet.toList ++ pending
    if let .inductInfo iv := ci then
      pending := iv.all ++ pending
  -- Each imported module has its own namespace for elaborator-generated private names.
  -- Carry the checked kernel environment across module boundaries, as loading a module does.
  let mut groups : Std.HashMap Nat (Std.HashMap Name ConstantInfo) := {}
  for (n, ci) in additions.toList do
    let some idx := src.getModuleIdxFor? n | throwError "Missing module for {n}"
    groups := groups.insert idx.toNat ((groups.getD idx.toNat {}).insert n ci)
  let mut checked := base
  for idx in [:src.header.moduleNames.size] do
    if let some group := groups[idx]? then
      let next ← checked.replay group
      checked := Environment.ofKernelEnv next.toKernelEnv
  let finalConstants := checked.toKernelEnv.constants
  for (n, _) in additions.toList do
    unless finalConstants.contains n do throwError "Missing after kernel replay: {n}"
  for n in replayTargets do
    unless finalConstants.contains n do throwError "Kernel replay did not construct {n}"
    logInfo m!"Replayed target {n}"
  logInfo m!"Kernel replay accepted {additions.size} declarations above Lean Init"
