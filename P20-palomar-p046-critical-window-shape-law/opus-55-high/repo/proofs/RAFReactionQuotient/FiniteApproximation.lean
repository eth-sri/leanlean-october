module

public import proofs.RAFReactionQuotient.InfiniteDock
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Cylinders

public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem quotientClosure_pullback {n L : ℕ} (q : RepositoryChannel n → Prop) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions $ fun r => q $ splitToQuotient r) := by
  have he : fieldOR splitToQuotient (q $ splitToQuotient ·) = q := by
    funext j
    exact propext $ quotient_mark_pullback_OR q j
  rw [← quotientClosure_OR,he]

end RAFReactionQuotient
