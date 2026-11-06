module

public import NearlyMinimax.HighUnionRawFisher
public import NearlyMinimax.CompleteSourceDensityProduct
public import NearlyMinimax.CompleteSourceSaddleMassTail
public import NearlyMinimax.HighPriorRisk
public import NearlyMinimax.HighParameterPath
public import NearlyMinimax.HighUnionSourceUniformModel
public import NearlyMinimax.HighUnionObservationGuards
public import NearlyMinimax.TernaryEffectiveInterval
public import NearlyMinimax.ScoreEnergyIntegral

@[expose] public section

/-! The true complete source, canonical reset law and local spatial
numerators imply the original minimax path lower bound uniformly over
extension domains. Mass-law invariance, exceptional tails, model legality
and all score/path assumptions are conclusions of the actual construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

abbrev HighCompleteSourceHistory {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    [NeZero k] [LinearOrder (HighWindowLabels d k)] (Cfr lam ell N mu : ℝ) :=
  HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
    (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) Cfr lam ell N mu))

end NearlyMinimax
