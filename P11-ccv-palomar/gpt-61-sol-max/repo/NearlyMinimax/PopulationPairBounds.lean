module

public import NearlyMinimax.PaperSeriesAllocation
public import NearlyMinimax.PairPilotAssumptions

@[expose] public section

/-! Actual population coefficient bounds on the genuine weighted pair design.
The fine grid may be any dyadic refinement of the population terminal level. -/
noncomputable section
open Filter MeasureTheory Set
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPopulationCoefficients_first {d } (C : ModelConstants d)
    θ J m w :
    dyadicPopulationCoefficients C θ J m w 0 = 1 := rfl

theorem regularPairDesignMeasure_dyadic_cell_ae {d } (θ : RegressionParameter d) J :
    ∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ J) (by positivity),
      w.2 ∈ dyadicPilotCell J w.1 := by
  apply regularPairDesignMeasure_ae_of_supported
  filter_upwards [] with w hw
  change regularGridCell ((2 : ℕ) ^ J) (by positivity) w.2 =
    regularGridCell ((2 : ℕ) ^ J) (by positivity) w.1
  by_contra h
  apply hw
  simp [sameLabelKernel, Ne.symm h]

end NearlyMinimax
