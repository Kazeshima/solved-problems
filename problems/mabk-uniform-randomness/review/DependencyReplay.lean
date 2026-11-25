import Lean.Replay
import Lean.Util.Path

open Lean

private partial def collectProof (source base : Environment) (name : Name)
    (selected : IO.Ref (Std.HashMap Name ConstantInfo)) : IO Unit := do
  if base.contains name || (← selected.get).contains name then return
  let some ci := source.find? name | throw <| IO.userError s!"Missing dependency {name}"
  if ci.isUnsafe || ci.isPartial then throw <| IO.userError s!"Non-replayable dependency {name}"
  if ci matches .axiomInfo _ then throw <| IO.userError s!"Axiom outside Init: {name}"
  selected.modify (·.insert name ci)
  for dep in ci.getUsedConstantsAsSet do collectProof source base dep selected
  if let .inductInfo i := ci then
    for other in i.all do collectProof source base other selected

/-- Recheck the proof and all its dependencies above Lean's Init. In particular,
the mathlib theorems used by this proof are submitted to the kernel here. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let moduleName := (args[0]?.getD "MABKCore").toName
  let target := (args[1]?.getD "MABK.conjecture1").toName
  let base ← importModules #[{module := `Init}] {} 0
  let source ← importModules #[{module := moduleName}] {} 0
  let ref ← IO.mkRef (∅ : Std.HashMap Name ConstantInfo)
  collectProof source base target ref
  let selected ← ref.get
  if !selected.contains target then throw <| IO.userError "The target was already in Init"
  if target == `MABK.conjecture1 then
    let milestones := #[`MABK.joint_spectral_bound, `MABK.polarization_diagonal_max,
      `MABK.canonical_disk_norm, `MABK.torus_disk_two, `MABK.angle_contact, `MABK.paper_curve,
      `MABK.zero_correlator_bound, `MABK.ghz_probability, `MABK.tensor_realization]
    for n in milestones do
      if !selected.contains n then throw <| IO.userError s!"Missing proof stage {n}"
      IO.println s!"Final proof uses {n}"
    if selected.contains `MABK.finite_phase_mixture_bound then
      throw <| IO.userError "Unexpected finite-mixture proof dependency"
  IO.println s!"Submitting {selected.size} declarations for {target} to the kernel, with only Init imported."
  let mut modules : Std.HashMap Nat (Std.HashMap Name ConstantInfo) := ∅
  for (n,ci) in selected.toList do
    let some idx := source.getModuleIdxFor? n | throw <| IO.userError s!"Missing module for {n}"
    modules := modules.insert idx.toNat ((modules.getD idx.toNat ∅).insert n ci)
  let mut checked := base
  for i in [:source.allImportedModuleNames.size] do
    if let some constants := modules[i]? then
      let next ← Environment.replay constants checked
      checked := Environment.ofKernelEnv next.toKernelEnv
  for (n, _) in selected.toList do
    if (checked.toKernelEnv.find? n).isNone then throw <| IO.userError s!"Missing replayed dependency {n}"
  IO.println s!"Dependency replay succeeded for {target}, including declarations from {modules.size} modules above Init."
