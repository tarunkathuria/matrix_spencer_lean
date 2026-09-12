import MatrixSpencer.DyadicOwnerSDP

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace DyadicSDPPrimitiveCheck
open MatrixSpencer
open MatrixSpencer.DyadicSDPCoordinates

/-- Independently written concrete affine-LMI maximum statement. -/
theorem real_affine_SDP_maximum {d N : ℕ} (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (m : ℕ) (hm : 1≤m) (θ : ℝ) (hθ : 0<θ) :
    ∃x : EuclideanSpace ℝ (Fin (dimension m a)),
      (∀b : DyadicSDPAffineData.Constraint m,
        (KSFullManuscriptAffinePSD.matrixAt
          (DyadicSDPAffineData.data m a A hA C hC (DyadicOwnerSDP.center a) b) x).PosSemidef) ∧
      DyadicSDPAffineObjective.offset m a H θ (DyadicOwnerSDP.center a) +
        ⟪DyadicSDPAffineObjective.coefficient m a H θ,x⟫_ℝ = dyadicOwnerPotential H A C m θ ∧
      ∀y : EuclideanSpace ℝ (Fin (dimension m a)),
        (∀b : DyadicSDPAffineData.Constraint m,
          (KSFullManuscriptAffinePSD.matrixAt
            (DyadicSDPAffineData.data m a A hA C hC (DyadicOwnerSDP.center a) b) y).PosSemidef) →
        DyadicSDPAffineObjective.offset m a H θ (DyadicOwnerSDP.center a) +
          ⟪DyadicSDPAffineObjective.coefficient m a H θ,y⟫_ℝ ≤
        DyadicSDPAffineObjective.offset m a H θ (DyadicOwnerSDP.center a) +
          ⟪DyadicSDPAffineObjective.coefficient m a H θ,x⟫_ℝ :=
  DyadicOwnerSDP.exists_maximizer m a H A hA C hC hm hθ

/-- Independently written exact counts of actual real coordinate/LMI arrays. -/
theorem exact_real_program_size {d : ℕ} (a : Fin d) (m : ℕ) :
    dimension m a = (m+3)*d^2-1 ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) = 2*m+1 ∧
    DyadicSDPAffineData.matrixSize (Fin d) = 4*d ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) * (dimension m a+1) *
      (DyadicSDPAffineData.matrixSize (Fin d))^2 = 16*(2*m+1)*(m+3)*d^4 := by
  simpa only [Fintype.card_fin, DyadicSDPProgramSize.variableCount,
    DyadicSDPProgramSize.constraintCount, DyadicSDPProgramSize.blockOrder] using
    DyadicOwnerSDP.actual_size_bounds m a
end DyadicSDPPrimitiveCheck

#print axioms DyadicSDPPrimitiveCheck.real_affine_SDP_maximum
#print axioms DyadicSDPPrimitiveCheck.exact_real_program_size
#print MatrixSpencer.DyadicOwnerSDP.exists_maximizer
#print MatrixSpencer.DyadicOwnerSDP.rectangular_exists_maximizer
#print MatrixSpencer.DyadicOwnerSDP.rectangular_size_bounds
#print axioms MatrixSpencer.DyadicSDPTracePower.Chain
#print axioms MatrixSpencer.DyadicSDPTracePower.power
#print axioms MatrixSpencer.DyadicSDPTracePower.canonical
#print axioms MatrixSpencer.DyadicSDPTracePower.canonical_last
#print axioms MatrixSpencer.DyadicSDPTracePower.power_zero
#print axioms MatrixSpencer.DyadicSDPTracePower.power_posSemidef
#print axioms MatrixSpencer.DyadicSDPTracePower.canonical_chain
#print axioms MatrixSpencer.DyadicSDPTracePower.chain_trace_le
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.Feasible
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.value
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.objective
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.feasible_density
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.coefficient_nonneg
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.feasible_value_le
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.fixed_density_attainment
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.feasible_value_le_densityPotential
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.kraus_SDP_exact
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.values
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.kraus_isGreatest
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.kraus_sSup_eq
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.covariance_feasible_iff
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.feasible_value_le_ownerPotential
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.owner_SDP_exact
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.owner_isGreatest
#print axioms MatrixSpencer.DyadicOwnerSDPIdentity.owner_sSup_eq
#print axioms MatrixSpencer.DyadicSDPCoordinates.Index
#print axioms MatrixSpencer.DyadicSDPCoordinates.densityLinear
#print axioms MatrixSpencer.DyadicSDPCoordinates.auxiliaryLinear
#print axioms MatrixSpencer.DyadicSDPCoordinates.fidelityLinear
#print axioms MatrixSpencer.DyadicSDPCoordinates.density
#print axioms MatrixSpencer.DyadicSDPCoordinates.chain
#print axioms MatrixSpencer.DyadicSDPCoordinates.chainLinear
#print axioms MatrixSpencer.DyadicSDPCoordinates.chain_zero
#print axioms MatrixSpencer.DyadicSDPCoordinates.chain_succ
#print axioms MatrixSpencer.DyadicSDPCoordinates.chain_affine
#print axioms MatrixSpencer.DyadicSDPCoordinates.chain_hermitian
#print axioms MatrixSpencer.DyadicSDPCoordinates.chainLinear_hermitian
#print axioms MatrixSpencer.DyadicSDPCoordinates.encode
#print axioms MatrixSpencer.DyadicSDPCoordinates.density_trace
#print axioms MatrixSpencer.DyadicSDPCoordinates.density_encode
#print axioms MatrixSpencer.DyadicSDPCoordinates.auxiliary_encode
#print axioms MatrixSpencer.DyadicSDPCoordinates.fidelity_encode
#print axioms MatrixSpencer.DyadicSDPCoordinates.dimension
#print axioms MatrixSpencer.DyadicSDPCoordinates.Space
#print axioms MatrixSpencer.DyadicSDPCoordinates.entries
#print axioms MatrixSpencer.DyadicSDPCoordinates.coordinates
#print axioms MatrixSpencer.DyadicSDPCoordinates.entries_coordinates
#print axioms MatrixSpencer.DyadicSDPCoordinates.unit
#print axioms MatrixSpencer.DyadicSDPCoordinates.sum_units
#print axioms MatrixSpencer.DyadicSDPCoordinates.dimension_eq
#print axioms MatrixSpencer.DyadicSDPAffineData.Constraint
#print axioms MatrixSpencer.DyadicSDPAffineData.RealIndex
#print axioms MatrixSpencer.DyadicSDPAffineData.matrixSize
#print axioms MatrixSpencer.DyadicSDPAffineData.block
#print axioms MatrixSpencer.DyadicSDPAffineData.source_add
#print axioms MatrixSpencer.DyadicSDPAffineData.source_smul
#print axioms MatrixSpencer.DyadicSDPAffineData.source_hermitian
#print axioms MatrixSpencer.DyadicSDPAffineData.block_add
#print axioms MatrixSpencer.DyadicSDPAffineData.block_smul
#print axioms MatrixSpencer.DyadicSDPAffineData.block_hermitian
#print axioms MatrixSpencer.DyadicSDPAffineData.complexLinear
#print axioms MatrixSpencer.DyadicSDPAffineData.realLinear
#print axioms MatrixSpencer.DyadicSDPAffineData.finiteLinear
#print axioms MatrixSpencer.DyadicSDPAffineData.constant
#print axioms MatrixSpencer.DyadicSDPAffineData.data
#print axioms MatrixSpencer.DyadicSDPAffineData.matrixAt_eq
#print axioms MatrixSpencer.DyadicSDPAffineData.matrixAt_physical
#print axioms MatrixSpencer.DyadicSDPAffineData.target
#print axioms MatrixSpencer.DyadicSDPAffineData.convex_target
#print axioms MatrixSpencer.DyadicSDPAffineData.target_iff
#print axioms MatrixSpencer.DyadicSDPAffineData.constraint_count
#print axioms MatrixSpencer.DyadicSDPAffineData.matrixSize_eq
#print axioms MatrixSpencer.DyadicSDPAffineObjective.valueLinear
#print axioms MatrixSpencer.DyadicSDPAffineObjective.coefficient
#print axioms MatrixSpencer.DyadicSDPAffineObjective.offset
#print axioms MatrixSpencer.DyadicSDPAffineObjective.objective
#print axioms MatrixSpencer.DyadicSDPAffineObjective.coefficient_inner
#print axioms MatrixSpencer.DyadicSDPAffineObjective.value_eq_affine
#print axioms MatrixSpencer.DyadicSDPAffineObjective.target
#print axioms MatrixSpencer.DyadicSDPAffineObjective.feasible_onto
#print axioms MatrixSpencer.DyadicSDPAffineObjective.values
#print axioms MatrixSpencer.DyadicSDPAffineObjective.values_eq
#print axioms MatrixSpencer.DyadicSDPAffineObjective.owner_exists_maximizer
#print axioms MatrixSpencer.DyadicSDPAffineObjective.owner_isGreatest
#print axioms MatrixSpencer.DyadicSDPAffineObjective.owner_sSup_eq
#print axioms MatrixSpencer.DyadicSDPProgramSize.variableCount
#print axioms MatrixSpencer.DyadicSDPProgramSize.constraintCount
#print axioms MatrixSpencer.DyadicSDPProgramSize.blockOrder
#print axioms MatrixSpencer.DyadicSDPProgramSize.denseCoefficients
#print axioms MatrixSpencer.DyadicSDPProgramSize.variableCount_add_one
#print axioms MatrixSpencer.DyadicSDPProgramSize.denseCoefficients_eq
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_depth_le
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_variableCount_le
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_constraintCount_le
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_blockOrder
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_denseCoefficients_le
#print axioms MatrixSpencer.DyadicSDPProgramSize.rectangular_sizes
#print axioms MatrixSpencer.DyadicOwnerSDP.center
#print axioms MatrixSpencer.DyadicOwnerSDP.center_trace
#print axioms MatrixSpencer.DyadicOwnerSDP.feasible
#print axioms MatrixSpencer.DyadicOwnerSDP.objective
#print axioms MatrixSpencer.DyadicOwnerSDP.feasible_eq
#print axioms MatrixSpencer.DyadicOwnerSDP.convex_feasible
#print axioms MatrixSpencer.DyadicOwnerSDP.exists_maximizer
#print axioms MatrixSpencer.DyadicOwnerSDP.sSup_eq
#print axioms MatrixSpencer.DyadicOwnerSDP.actual_size_bounds
#print axioms MatrixSpencer.DyadicOwnerSDP.rectangular_size_bounds
#print axioms MatrixSpencer.DyadicOwnerSDP.rectangular_exists_maximizer
