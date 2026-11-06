module

public import proofs.RAFCriticalWindowQuantitative.SourceContract

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open Filter
open scoped Topology

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) $ profile.2-source.1

theorem interval_error {P S : ℝ} {u v : ℚ × ℚ} {X : Prop} (hP : (u.1 : ℝ) ≤ P ∧ P ≤ u.2)
    (hS : (v.1 : ℝ) ≤ S ∧ S ≤ v.2 ∧ X) : |P-S| ≤ (rationalIntervalError u v : ℝ) := by
  simp only [rationalIntervalError]
  push_cast
  grind

end RAFCriticalWindowQuantitative
