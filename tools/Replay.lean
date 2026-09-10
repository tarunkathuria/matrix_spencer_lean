import Lean.CoreM
import Lean.Replay
import Lean.Util.CollectAxioms

/-!
A small replay driver for the installed Lean 4.24 API.

It uses the installed runtime's `Lean.Environment.replay`, which sends safe
declarations back through the same Lean kernel. This is not an independent
kernel implementation. The final-theorem type and dependency checks remain
separate and mandatory in check_proof.py.

The module-loading pattern follows Lean's LeanChecker driver (MIT license,
copyright 2023 Kim Morrison; authors Kim Morrison and Sebastian Ullrich).
-/

open Lean

unsafe def replayAgainstImports (moduleName : Name) : IO Unit := do
  let moduleFile ← findOLean moduleName
  unless (← moduleFile.pathExists) do
    throw <| IO.userError s!"Missing compiled module: {moduleName}"
  let mut files := #[moduleFile]
  let serverFile := OLeanLevel.server.adjustFileName moduleFile
  if (← serverFile.pathExists) then
    files := files.push serverFile
    let privateFile := OLeanLevel.private.adjustFileName moduleFile
    if (← privateFile.pathExists) then
      files := files.push privateFile
  let parts ← readModuleDataParts files
  let some first := parts[0]? | throw <| IO.userError "Empty module data"
  let some last := parts[parts.size - 1]? | throw <| IO.userError "Empty module data"
  let (_, state) ← (importModulesCore first.1.imports).run
  let env ← finalizeImport state first.1.imports {} 0 false false
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  for name in last.1.constNames, info in last.1.constants do
    match info with
    | .axiomInfo _ =>
      throw <| IO.userError s!"Forbidden project axiom declaration in {moduleName}: {name}"
    | _ => pure ()
    declarations := declarations.insert name info
  try
    let replayed ← Lean.Environment.replay declarations env
    let audit : CollectAxioms.M Unit := do
      for (name, _) in declarations.toList do
        CollectAxioms.collect name
    let (_, auditState) := (audit.run replayed).run {}
    for dependency in auditState.axioms do
      unless dependency == `propext || dependency == `Classical.choice || dependency == `Quot.sound do
        throw <| IO.userError s!"Disallowed dependency in {moduleName}: {dependency}"
    IO.println s!"REPLAYED {moduleName}: {declarations.size} local declarations loaded; safe nonpartial declarations checked against imports"
    IO.println s!"PROJECT_AXIOMS_CHECKED {moduleName}: only allowed standard dependencies across all local declarations"
    (← IO.getStdout).flush
  finally
    env.freeRegions

unsafe def replayProjectClosure (moduleName : Name) (seen : IO.Ref (Std.HashSet String)) : IO Unit := do
  withImportModules #[{ module := moduleName }] {} fun env => do
    let mut checked := 0
    let mut matched := 0
    for importedName in env.header.moduleNames do
      if (`MatrixSpencer).isPrefixOf importedName then
        matched := matched + 1
        -- Imported names can refer into regions released after this callback.
        -- Keep an owned string copy across module-closure imports instead.
        let ownedKey := String.mk importedName.toString.toList
        unless (← seen.get).contains ownedKey do
          replayAgainstImports importedName
          seen.modify (·.insert ownedKey)
          checked := checked + 1
    if matched == 0 then
      throw <| IO.userError "No MatrixSpencer project modules found in the import closure"
    IO.println s!"PROJECT_CLOSURE_REPLAYED: {matched} MatrixSpencer modules ({checked} newly replayed)"
    (← IO.getStdout).flush

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.contains "--fresh" then
    IO.eprintln "Fresh-all replay is unsupported by this Lean 4.24 adapter: the installed replay implementation has duplicate-normalized-name failures. No fresh-all verification is claimed."
    return 2
  let names := args
  if names.isEmpty then
    IO.eprintln "Usage: lean --run tools/Replay.lean Module ..."
    return 2
  let seen ← IO.mkRef ({} : Std.HashSet String)
  for name in names do
    let moduleName := name.toName
    if moduleName.isAnonymous || name.startsWith "-" then
      throw <| IO.userError s!"Invalid module name: {name}"
    replayProjectClosure moduleName seen
  return 0
