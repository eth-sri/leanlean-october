module

public import proofs.HordijkSteelThreshold.StaticSurvivalLeftContinuity

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem staticSurvival_le_finite_escape (a : I) (K : ℕ) :
    staticSurvival a ≤ staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) := by
  rw [finite_static_escape_measure_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

end HordijkSteelThreshold
