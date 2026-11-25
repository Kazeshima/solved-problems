import Lean.Replay
import Lean.Util.Path

open Lean

private structure ProjectData where
  visited : NameSet := ∅
  external : NameSet := ∅
  modules : Array (Name × Array ConstantInfo) := #[]
  compilerHelpers : Nat := 0

private partial def gather (moduleName : Name) (data : IO.Ref ProjectData) : IO Unit := do
  if (← data.get).visited.contains moduleName then return
  data.modify fun d => {d with visited := d.visited.insert moduleName}
  let (mod, _) ← readModuleData (← findOLean moduleName)
  for dep in mod.imports do
    if (`MABKCore).isPrefixOf dep.module then gather dep.module data
    else data.modify fun d => {d with external := d.external.insert dep.module}
  let mut mathematical := #[]
  for ci in mod.constants do
    if ci.isUnsafe || ci.isPartial then
      let name := ci.name.toString
      if (name.splitOn "._cstage").length < 2 && (name.splitOn "._spec_").length < 2 then
        throw <| IO.userError s!"Non-replayable project declaration {ci.name}"
      IO.println s!"Compiler helper outside the logic: {ci.name}"
      data.modify fun d => {d with compilerHelpers := d.compilerHelpers+1}
    else
      if ci matches .axiomInfo _ then throw <| IO.userError s!"Project axiom {ci.name}"
      mathematical := mathematical.push ci
  data.modify fun d => {d with modules := d.modules.push (moduleName,mathematical)}

/-- Use the pinned Lean kernel to check the serialized project declarations
again, starting from an environment containing only external dependencies. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let root := (args.headD "MABKCore").toName
  let state ← IO.mkRef ({} : ProjectData)
  gather root state
  let d ← state.get
  let imports := d.external.toList.toArray.map fun n => ({module := n} : Import)
  let mut checked ← importModules imports {} 0
  let mut count := 0
  for (moduleName,batch) in d.modules do
    let mut constants : Std.HashMap Name ConstantInfo := ∅
    for ci in batch do
      if (checked.toKernelEnv.find? ci.name).isSome then throw <| IO.userError s!"Project declaration already in base: {ci.name}"
      constants := constants.insert ci.name ci
    let next ← Environment.replay constants checked
    -- Reset the elaborator's per-module table of private names. Preserve precisely
    -- the kernel environment that just checked the preceding module.
    checked := Environment.ofKernelEnv next.toKernelEnv
    for ci in batch do
      if (checked.toKernelEnv.find? ci.name).isNone then throw <| IO.userError s!"Missing replayed declaration: {ci.name}"
    count := count + batch.size
    IO.println s!"{moduleName}: {batch.size} declarations rechecked"
  IO.println s!"Kernel replay succeeded for {count} declarations across {d.visited.size} project modules."
  IO.println s!"Compiler-generated staging helpers outside the logic: {d.compilerHelpers}."
