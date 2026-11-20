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

variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (J : ℕ)

theorem regularPairDesignMeasure_dyadic_cell_ae :
    ∀ᵐ w ∂dyadicPairDesignMeasure θ J,
      w.2 ∈ dyadicPilotCell J w.1 := by
  apply regularPairDesignMeasure_ae_of_supported
  filter_upwards [] with w hw
  by_contra h
  apply hw
  simp [sameLabelKernel, Ne.symm h]

end NearlyMinimax
