import MatrixSpencer.DyadicManuscriptAnalyticAlgorithm
open Matrix MatrixSpencer
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
namespace MSRectangularAnalyticPrimitive
variable {N D : ℕ} [NeZero D]

theorem rectangular_return (hN : 0 < N) (hND : N ≤ D)
    (A : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ i, (A i)ᴴ = A i)
    (hbound : ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ 1) (r : ℕ)
    (z : (DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).Draws)
    (σ : Fin N → ℝ)
    (hout : (DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).value z = some σ) :
    (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (∑ i, (σ i : ℂ) • A i)‖ ≤
        6796548*Real.sqrt ((N : ℝ)*Real.log (2*(D : ℝ)/(N : ℝ))) :=
  DyadicManuscriptAnalyticAlgorithm.output_sound hN hND A hA hbound r z σ hout

theorem rectangular_success (hN : 0 < N) (hND : N ≤ D)
    (A : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ i, (A i)ᴴ = A i)
    (hbound : ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ 1) :
    let r := (N+1)*(RectangularEpochParameters.count (RectangularTunedParameters.coefficient N D))+1
    (1 : ℝ)/2 ≤ ∑ z,
      (DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).weight z *
        (if ((DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).value z).isSome
          then 1 else 0) :=
  DyadicManuscriptAnalyticAlgorithm.constant_success hN hND A hA hbound

theorem rectangular_weights (hN : 0 < N) (hND : N ≤ D)
    (A : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀i,(A i)ᴴ=A i)
    (hbound : ∀i,‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖≤1) (r : ℕ) :
    (∀z,(DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).weight z≥0) ∧
      (∑z,(DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).weight z)=1 :=
  ⟨(DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).weight_nonneg,
    (DyadicManuscriptAnalyticAlgorithm.output hN hND A hA hbound r).weight_sum⟩

#print axioms rectangular_return
#print axioms rectangular_success
#print axioms rectangular_weights
end MSRectangularAnalyticPrimitive
