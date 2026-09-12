import MatrixSpencer.DyadicManuscriptAnalyticAlgorithm
import Lean

open Lean
namespace MSRectangularAnalyticRoutes

def inProject (n : Name) : Bool :=
  (`MatrixSpencer).isPrefixOf n || n.toString.startsWith "_private.MatrixSpencer."

def inspectedData (n : Name) : Bool :=
  inProject n || (`Matrix.IsHermitian).isPrefixOf n || n == `CFC.sqrt

-- A syntactic operation-route guard. Theorem bodies are excluded from the
-- data scan; this is not an extraction or real-RAM execution theorem.
partial def dataClosure (todo : List Name) (seen : NameSet := {}) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← dataClosure rest seen
    let info ← getConstInfo n
    let children := match info with
      | .thmInfo _ => []
      | _ => info.value?.toList.flatMap (fun e => e.getUsedConstants.toList.filter inspectedData)
    dataClosure (children ++ rest) (seen.insert n)

partial def proofClosure (todo : List Name) (seen : NameSet := {}) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n || !inProject n then return ← proofClosure rest seen
    let info ← getConstInfo n
    let children := info.type.getUsedConstants.toList ++
      info.value?.toList.flatMap (fun e => e.getUsedConstants.toList)
    proofClosure (children ++ rest) (seen.insert n)

run_cmd Lean.Elab.Command.liftCoreM do
  let data ← dataClosure [`MatrixSpencer.DyadicManuscriptAnalyticAlgorithm.output]
  for n in [`MatrixSpencer.DyadicManuscriptFullSigning.output,
      `MatrixSpencer.DyadicManuscriptFullSigning.analyticReports,
      `MatrixSpencer.MSManuscriptAdaptive.run] do
    unless data.contains n do throwError "Missing declared analytic sampling operation: {n}"
  let proof ← proofClosure [`MatrixSpencer.DyadicManuscriptAnalyticAlgorithm.output_sound,
    `MatrixSpencer.DyadicManuscriptAnalyticAlgorithm.constant_success]
  for n in [`MatrixSpencer.DyadicManuscriptFullSigning.output_sound,
      `MatrixSpencer.DyadicManuscriptFullSigning.output_event_probability,
      `MatrixSpencer.MSManuscriptRetryBudget.failure_budget] do
    unless proof.contains n do throwError "Missing actual sampler success proof: {n}"
  for n in [`MatrixSpencer.matrix_spencer_square, `MatrixSpencer.matrix_spencer_rectangular,
      `MatrixSpencer.kadison_singer_eighth, `MatrixSpencer.kadison_singer_spin_mixed] do
    if proof.contains n then throwError "Prior final existence substituted: {n}"
  logInfo m!"MS_RECTANGULAR_ANALYTIC_ROUTE_CHECKED {data.toList.length} data declarations; {proof.toList.length} project proof declarations; analytic preparation and exact reports explicitly retained"
end MSRectangularAnalyticRoutes
