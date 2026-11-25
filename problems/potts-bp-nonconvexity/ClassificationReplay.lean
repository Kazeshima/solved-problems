import PottsClassification
import Lean.Replay
import Lean.Util.CollectAxioms

/-! Independent kernel replay of the cited proof terms above the pinned Lean Init library.
This file is a verifier. The mathematical modules do not import it. -/
open Lean

private def replayTargets : List Name :=
  [``PottsBP.question4_false, ``PottsBP.source_question4_false,
   ``PottsBP.source_nonconvex_general, ``PottsBP.productLaw_isProbability,
   ``PottsBP.sourceImage_eq_generalImage, ``PottsBP.sourceWeight_eq_rawWeight,
   ``PottsBP.admissibleSourceImage_eq_generalImage, ``PottsBP.admissibleSourceImage_eq_sourceImage_diff_zero,
   ``PottsBP.legacy_zero_image, ``PottsBP.source_convex_beta_one, ``PottsBP.source_convex_one_neighbor,
   ``PottsBP.source_convex_two_colors, ``PottsBP.source_convex_three_colors,
   ``PottsBP.source_image_zero_beta_eq_simplex, ``PottsBP.source_nonconvex_positive_beta,
   ``PottsBP.source_nonconvex_iff, ``PottsBP.source_nonconvex_iff_on_defined_outputs,
   ``PottsBP.Classification.column_tangent, ``PottsBP.Classification.fractional_at_tangent,
   ``PottsBP.Classification.edge_cross, ``PottsBP.Classification.height_intermediate,
   ``PottsBP.Classification.three_fill, ``PottsBP.sourceImage_eq_admissible_positive,
   ``PottsBP.paper_classification]

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
  -- Match each top-level theorem/lemma in the new source modules against a theorem
  -- actually reconstructed above. This also covers Lean-generated private names.
  let modules := [`PottsClassBasic, `PottsClassColumn, `PottsClassEdges, `PottsClassFiber,
    `PottsClassHot, `PottsClassThree, `PottsClassTwo, `PottsClassZero, `PottsClassification]
  let mut byModule : Std.HashMap (Name × String) Name := {}
  for (n, ci) in additions.toList do
    if let .thmInfo _ := ci then
      let some idx := src.getModuleIdxFor? n | continue
      let mod := src.header.moduleNames[idx]!
      if !modules.contains mod then continue
      if let .str _ leaf := privateToUserName n then
        byModule := byModule.insert (mod, leaf) n
  let mut covered := 0
  for mod in modules do
    let file ← IO.FS.readFile (mod.toString ++ ".lean")
    for line in file.splitOn "\n" do
      let words := line.splitOn " "
      let words := if words.head? == some "private" then words.drop 1 else words
      if let kind :: decl :: _ := words then
        if kind != "theorem" && kind != "lemma" then continue
        let leaf := (decl.splitOn ".").getLast!
        let some n := byModule[(mod, leaf)]? | throwError "Theorem omitted from kernel replay: {mod}/{decl}"
        unless finalConstants.contains n do throwError "Missing checked theorem: {n}"
        let axs ← collectAxioms n
        unless axs.all (fun k => [`propext, `Classical.choice, `Quot.sound].contains k) do
          throwError "Unapproved axiom in {n}: {axs}"
        logInfo m!"Covered theorem {mod}/{decl} with axioms {axs}"
        covered := covered + 1
  logInfo m!"Checked transitive axioms and replay membership for {covered} new named theorems"
  logInfo m!"Kernel replay accepted {additions.size} declarations above Lean Init"
