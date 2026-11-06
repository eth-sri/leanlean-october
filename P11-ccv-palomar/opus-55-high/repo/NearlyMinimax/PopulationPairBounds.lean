module

public import NearlyMinimax.PaperSeriesAllocation
public import RoughRegime.Macro
public import NearlyMinimax.PairPilotAssumptions
public import RoughRegime.Notation

𝗍

/-! Actual population coefficient bounds on the genuine weighted pair design.
The fine grid may be any dyadic refinement of the population terminal level. -/
open Filter MeasureTheory Set
𝚻
𝚨
𝚭
𝚩

theorem dyadicPopulationCoefficients_first C
    (θ : RegressionParameter d) J m w :
    𝘺₁ w 0 = 1 := by
  rfl

theorem regularPairDesignMeasure_dyadic_cell_ae (θ : RegressionParameter d) J :
    ∀ᵐ w ∂regularPairDesignMeasure θ 𝖵₂ 𝖠₃ ,
      w.2 ∈ dyadicPilotCell J w.1 := by
  apply regularPairDesignMeasure_ae_of_supported
  filter_upwards [] with w hw
  by_contra h
  apply hw
  simp [sameLabelKernel, Ne.symm h]
