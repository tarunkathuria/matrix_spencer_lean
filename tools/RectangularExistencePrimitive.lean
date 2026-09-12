import MatrixSpencer.RectangularMain
import Lean

open scoped BigOperators Matrix

namespace MatrixSpencerVerification
def ExpectedRectangularStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n d : ℕ), 1 ≤ n → n ≤ d →
      ∀ (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
        (∀ i, (B i).IsHermitian) →
        (∀ i, ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (B i)‖ ≤ 1) →
        ∃ ε : Fin n → ℝ,
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
            (∑ i : Fin n, (ε i : ℂ) • B i)‖ ≤ C * Real.sqrt ((n : ℝ) * Real.log (2 * (d : ℝ) / (n : ℝ)))
end MatrixSpencerVerification

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo `MatrixSpencer.matrix_spencer_rectangular
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "The final target must be a theorem declaration."
  unless (← Lean.Meta.isDefEq info.type (Lean.mkConst `MatrixSpencer.rectangularStatement)) do
    throwError "The final theorem declaration has the wrong type."
  unless (← Lean.Meta.isDefEq info.type
      (Lean.mkConst `MatrixSpencerVerification.ExpectedRectangularStatement)) do
    throwError "The final theorem does not match the independently frozen mathematical statement."

#check (MatrixSpencer.matrix_spencer_rectangular : MatrixSpencer.rectangularStatement)
example : MatrixSpencerVerification.ExpectedRectangularStatement := MatrixSpencer.matrix_spencer_rectangular
#print MatrixSpencerVerification.ExpectedRectangularStatement
#print MatrixSpencer.rectangularStatement
#print MatrixSpencer.rectangularStatementWithConstant
#eval IO.println "RECTANGULAR_ORIGINAL_AXIOMS_BEGIN"
#print axioms MatrixSpencer.matrix_spencer_rectangular
#eval IO.println "RECTANGULAR_ORIGINAL_AXIOMS_END"
