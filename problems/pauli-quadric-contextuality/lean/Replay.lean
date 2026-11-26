import Quadric
import Lean.Replay
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Independent kernel replay of the cited proof terms above the pinned Lean Init library.
This file is a verifier. The mathematical modules do not import it. -/
open Lean

private def replayTargets : List Name :=
  [``Quadric.contextuality_bounds, ``Quadric.contextuality_limit,
   ``Quadric.Four.degree_four, ``Quadric.Four.flat_iff_optimal,
   ``Quadric.Dual.plucker_points, ``Quadric.Dual.plucker_pencils, ``Quadric.Five.spectral_lower,
   ``Quadric.Four.optimal_iff_canonical_orbit, ``Quadric.Four.every_optimal_assignment,
   ``Quadric.Four.every_optimum_in_orbit,
   ``Quadric.Four.optimal_assignments_count, ``Quadric.Four.optimal_configurations_count,
   ``Quadric.Four.every_optimum_DW, ``Quadric.Four.classification,
   ``Quadric.Five.five_qubit_bounds,
   ``Quadric.Five.witness_count,
   ``Quadric.Five.degree_ne_6975975,
   ``Quadric.Five.canonical_centres5,
   ``Quadric.Five.five_from_full_four,
   ``Quadric.Five.one_elliptic_suffices,
   ``Quadric.Five.elliptic_reduction,
   ``Quadric.Five.exact_of_catalogues,
   ``Quadric.Five.Certificates.certificate_bound,
   ``Quadric.Five.Certificates.gram_positive,
   ``Quadric.Five.Census.LevelOne.coverage,
   ``Quadric.Five.Census.LevelOne.lengths,
   ``Quadric.Five.Census.LevelOne.section_census,
   ``Quadric.Five.Small.HyperplaneData.low_section,
   ``Quadric.Five.Certificates.all_42_certificates, ``Quadric.Five.Certificates.distinct_42,
   ``Quadric.Five.Census.LevelOne.distinct_survivors,
   ``Quadric.Five.Census.distinct_completion_count,
   ``Quadric.Five.hyperplane_profile_count,
   ``Quadric.Five.census_classification,
   ``Quadric.Five.all_low_signatures_in_orbits,
   ``Quadric.Five.every_low_restriction,
   ``Quadric.Five.degree_five]

private def optionalModuleLog : IO (Option IO.FS.Handle) := do
  let some path ← IO.getEnv "QUADRIC_REPLAY_MODULE_LOG" | return none
  let handle ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  handle.putStrLn "module\tdeclarations\telapsed_ms"
  handle.flush
  return some handle

run_cmd
  let logFile ← optionalModuleLog
  let started ← IO.monoMsNow
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
  IO.println s!"Starting kernel replay of {additions.size} declarations above Init for {replayTargets.length} targets"
  (← IO.getStdout).flush
  let mut checked := base
  for idx in [:src.header.moduleNames.size] do
    if let some group := groups[idx]? then
      let next ← checked.replay group
      checked := Environment.ofKernelEnv next.toKernelEnv
      let modName := src.header.moduleNames[idx]!
      if modName.toString.startsWith "Quadric" then
        if let some handle := logFile then
          let elapsed := (← IO.monoMsNow) - started
          handle.putStrLn s!"{modName}\t{group.size}\t{elapsed}"
          handle.flush
        IO.println s!"Kernel checked {modName} ({group.size} declarations)"
        (← IO.getStdout).flush
  let finalConstants := checked.toKernelEnv.constants
  for (n, _) in additions.toList do
    unless finalConstants.contains n do throwError "Missing after kernel replay: {n}"
  let auditAction : CollectAxioms.M Unit := replayTargets.forM CollectAxioms.collect
  let (_, audit) := (auditAction.run checked).run {}
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in audit.axioms do
    unless permitted.contains ax do throwError "Unapproved axiom in the replayed closure: {ax}"
  logInfo m!"Axioms in replayed targets: {audit.axioms.toList}"
  for n in replayTargets do
    unless finalConstants.contains n do throwError "Kernel replay did not construct {n}"
    logInfo m!"Replayed target {n}"
  logInfo m!"Kernel replay accepted {additions.size} declarations above Lean Init"
