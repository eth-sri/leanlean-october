
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
import proofs.HordijkSteelThreshold.StaticSeedMassBound
import proofs.HordijkSteelThreshold.AmbientEscapeBound
import proofs.HordijkSteelThreshold.SourceTerminalRAF
import proofs.HordijkSteelThreshold.RecordCylinderDeficit
import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.HordijkSteelThreshold.SplitPrefixIndependence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
import proofs.HordijkSteelThreshold.StaticEventContinuity
import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
import proofs.HordijkSteelThreshold.PositiveLowerPhase
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity



namespace HordijkSteelThreshold
open MeasureTheory unitInterval

theorem staticSurvival_le_finite_escape (a : I) (K : ℕ) :
    staticSurvival a ≤ staticReactionMeasure _ a (staticEscapeEvent 2 K) := by
  rw [finite_static_escape_measure_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

end HordijkSteelThreshold
