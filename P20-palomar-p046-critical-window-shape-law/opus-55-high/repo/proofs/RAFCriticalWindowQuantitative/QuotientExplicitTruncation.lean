module

public import proofs.RAFCriticalWindowQuantitative.ExplicitTruncation
public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical RAFReactionQuotient HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

theorem canonicalIndex_prefixIndex : PrefixIndex canonicalIndex := by
  simp [PrefixIndex, canonicalIndex]
  grind

noncomputable def quotientEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

end RAFCriticalWindowQuantitative
