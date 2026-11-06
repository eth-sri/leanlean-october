module

public import proofs.RAFCriticalWindowQuantitative.RecordIteration
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

end RAFCriticalWindowQuantitative
