import Shellsort
import Lean.Replay

/-! Recheck the transitive proof terms above the installed Init kernel environment. -/
open Lean

private def roots : List Name := [
  ``ShellMinimax.executed_maximum, ``ShellMinimax.actual_threshold_maximum, ``ShellMinimax.actual_threshold_path,
  ``ShellMinimax.binaryPass_card, ``ShellMinimax.binaryPass_mono, ``ShellMinimax.permutation_of_walk,
  ``ShellMinimax.distribution_actual, ``ShellMinimax.Certificate.certificate_sound,
  ``ShellMinimax.Certificate.legal_last,
  ``ShellMinimax.Reflected5.global, ``ShellMinimax.Reflected5.exact_minimizers,
  ``ShellMinimax.Witnesses.w17_9_attains, ``ShellMinimax.Witnesses.w18_17_attains,
  ``ShellMinimax.Witnesses.w19_9_attains, ``ShellMinimax.Witnesses.w20_11_attains,
  ``ShellMinimax.Witnesses.w21_9_attains, ``ShellMinimax.Witnesses.w21_20_attains,
  ``ShellMinimax.Witnesses.w22_5_attains, ``ShellMinimax.Witnesses.w22_7_attains,
  ``ShellMinimax.Witnesses.w22_8_attains, ``ShellMinimax.Witnesses.w22_9_attains,
  ``ShellMinimax.Witnesses.w22_21_attains, ``ShellMinimax.Witnesses.w23_9_attains,
  ``ShellMinimax.Witnesses.w23_22_attains, ``ShellMinimax.Reflected17.mask0,
  ``ShellMinimax.Reflected17.mask7, ``ShellMinimax.Block17.state0, ``ShellMinimax.Block17.state7]

run_cmd
  let src ← getEnv
  let mut checked ← importModules #[{module := `Init}] {} 0
  let mut todo := roots
  let mut seen : Std.HashSet Name := {}
  let mut modules : Std.HashMap Nat (Std.HashMap Name ConstantInfo) := {}
  repeat
    let name :: rest := todo | break
    todo := rest
    if checked.contains name || seen.contains name then continue
    let some decl := src.find? name | throwError "missing {name}"
    if decl.isUnsafe || decl.isPartial then throwError "unsafe or partial dependency {name}"
    if decl matches .axiomInfo _ then throwError "axiom outside Init: {name}"
    seen := seen.insert name
    let some idx := src.getModuleIdxFor? name | throwError "missing module for {name}"
    modules := modules.insert idx.toNat ((modules.getD idx.toNat {}).insert name decl)
    todo := decl.getUsedConstantsAsSet.toList ++ todo
    if let .inductInfo inductiveType := decl then todo := inductiveType.all ++ todo
  for i in [:src.header.moduleNames.size] do
    if let some group := modules[i]? then
      let next ← checked.replay group
      checked := Environment.ofKernelEnv next.toKernelEnv
  for name in seen.toList do
    unless checked.toKernelEnv.constants.contains name do throwError "kernel omitted {name}"
  logInfo m!"Kernel replay accepted {roots.length} roots and {seen.size} declarations above Init."
