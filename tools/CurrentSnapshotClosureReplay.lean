import Lean.CoreM
import Lean.Replay
import Lean.Util.CollectAxioms

/-! Replay an entire project closure in one kernel environment. The base
environment contains external imports only: no MatrixSpencer declaration is
assumed while replaying any other project declaration. The installed Lean replay scheduling code
orders the declaration graph and checks inductive constructors/recursors.
This uses the installed Lean kernel, not an independent implementation. -/
open Lean

/-- The only duplicates admitted are literally identical theorem records.
`TheoremVal`'s derived equality checks the constant name, universe parameters,
type, proof term, and mutual-block names. No theorem is accepted by type alone. -/
def identicalDuplicateTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo x, .thmInfo y => x == y
  | _, _ => false

/- Replay scheduling and constructor/recursor checks below are adapted verbatim
from Lean 4.24 Lean/Replay.lean, copyright 2023 Kim Morrison, Apache 2.0.
Changes: reset elaborator bookkeeping in addDecl, and read constructor/
recursor records directly from the checked kernel environment afterward.
Every declaration still goes through the installed kernel with checking on. -/
namespace RuntimeClosure

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  -- Reset elaborator-only private-name indexing. The complete checked kernel
  -- environment is preserved, and addDeclCore still checks the actual term.
  let kernelEnv := Environment.ofKernelEnv (← get).env.toKernelEnv
  match kernelEnv.addDeclCore 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info =>
        addDecl (Declaration.defnDecl   info)
      | .thmInfo    info =>
        addDecl (Declaration.thmDecl    info)
      | .axiomInfo  info =>
        addDecl (Declaration.axiomDecl  info)
      | .opaqueInfo info =>
        addDecl (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants[n]!))
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl (Declaration.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        addDecl (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.checked.get.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.checked.get.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay

/--
"Replay" some constants into an `Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.
-/
def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Environment) : IO Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s.env

end RuntimeClosure

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    throw <| IO.userError "Supply the complete project module closure"
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut imports : Array Import := #[]
  let mut importNames : Std.HashSet Name := {}
  let mut counts : Array (String × Nat) := #[]
  for arg in args do
    let name := arg.toName
    unless (`MatrixSpencer).isPrefixOf name do
      throw <| IO.userError s!"Invalid project module: {arg}"
    let file ← findOLean name
    let mut files := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if ← server.pathExists then
      files := files.push server
      let privateFile := OLeanLevel.private.adjustFileName file
      if ← privateFile.pathExists then files := files.push privateFile
    let parts ← readModuleDataParts files
    let some first := parts[0]? | throw <| IO.userError s!"Empty module: {arg}"
    let some last := parts[parts.size-1]? | throw <| IO.userError s!"Empty module: {arg}"
    for imp in first.1.imports do
      unless (`MatrixSpencer).isPrefixOf imp.module || importNames.contains imp.module do
        imports := imports.push imp
        importNames := importNames.insert imp.module
    for declName in last.1.constNames, info in last.1.constants do
      if let some previous := declarations[declName]? then
        unless identicalDuplicateTheorem previous info do
          throw <| IO.userError s!"Conflicting duplicate project declaration: {declName}"
      match info with
      | .axiomInfo _ => throw <| IO.userError s!"Forbidden project axiom: {declName}"
      | _ => pure ()
      declarations := declarations.insert declName info
    counts := counts.push (arg,last.1.constNames.size)
  let (_,state) ← (importModulesCore imports).run
  let env ← finalizeImport state imports {} 0 false false
  for name in env.header.moduleNames do
    if (`MatrixSpencer).isPrefixOf name then
      throw <| IO.userError s!"Project declaration leaked into external base: {name}"
  let originalDeclarations := declarations
  -- Lazily generated external congruence lemmas may also be serialized in
  -- project modules. Admit an external overlap only when its complete checked
  -- theorem record equals the stored one; never admit a type-only match.
  for (name,info) in declarations.toList do
    if let some external := env.checked.get.find? name then
      unless identicalDuplicateTheorem external info do
        throw <| IO.userError s!"Nonidentical overlap with external base: {name}"
      declarations := declarations.erase name
  IO.println s!"REPLAY_BASE_EXTERNAL_ONLY: {env.header.moduleNames.size} external modules; {declarations.size} project declarations to replay"
  (← IO.getStdout).flush
  try
    let replayed ← RuntimeClosure.replay declarations env
    -- Every safe nonpartial input record must have reached the checked kernel
    -- environment, including constructor/recursor records and exact duplicates.
    for (name,info) in originalDeclarations.toList do
      if !info.isUnsafe && !info.isPartial then
        unless (replayed.checked.get.find? name).isSome do
          throw <| IO.userError s!"Missing checked project declaration: {name}"
    let audit : CollectAxioms.M Unit := do
      for (name,_) in originalDeclarations.toList do CollectAxioms.collect name
    let (_,auditState) := (audit.run replayed).run {}
    for axiomName in auditState.axioms do
      unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
        throw <| IO.userError s!"Disallowed dependency: {axiomName}"
    for (name,count) in counts do
      IO.println s!"REPLAYED {name}: {count} local declarations loaded; safe nonpartial declarations checked from external base"
      IO.println s!"PROJECT_AXIOMS_CHECKED {name}: only allowed standard dependencies across all local declarations"
    IO.println s!"PROJECT_CLOSURE_REPLAYED: {counts.size} project modules from an external-only base"
    (← IO.getStdout).flush
  finally
    env.freeRegions
  return 0
