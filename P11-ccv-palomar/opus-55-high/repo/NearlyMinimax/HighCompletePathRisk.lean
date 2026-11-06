module

public import NearlyMinimax.HighUnionRawFisher
public import RoughRegime.Macro
public import NearlyMinimax.CompleteSourceDensityProduct
public import NearlyMinimax.CompleteSourceSaddleMassTail
public import NearlyMinimax.HighPriorRisk
public import NearlyMinimax.HighParameterPath
public import NearlyMinimax.HighUnionSourceUniformModel
public import NearlyMinimax.HighUnionObservationGuards
public import NearlyMinimax.TernaryEffectiveInterval
public import NearlyMinimax.ScoreEnergyIntegral
public import RoughRegime.Notation

𝗌

/-! The true complete source, canonical reset law and local spatial
numerators imply the original minimax path lower bound uniformly over
extension domains. Mass-law invariance, exceptional tails, model legality
and all score/path assumptions are conclusions of the actual construction. -/
𝚴
𝚳
𝚨
set_option maxHeartbeats 2000000
𝛀
𝚬
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

abbrev HighCompleteSourceHistory (C : ModelConstants d) (k D M q : ℕ)
    [NeZero k] [LinearOrder 𝙯] (Cfr lam ell N mu : ℝ) :=
  HistoryMarked 𝖫
    $ HighUnionMark $ SourceRowMark d D M q (C.densityLower+1/𝖧)
      (C.densityUpper-1/𝖧) Cfr lam ell N mu
