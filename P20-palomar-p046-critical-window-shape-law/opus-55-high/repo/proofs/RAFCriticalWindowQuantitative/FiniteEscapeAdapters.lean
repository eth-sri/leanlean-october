module

public import proofs.RAFCriticalWindowQuantitative.ExplicitTruncation
public import proofs.RAFCriticalWindowQuantitative.QuotientExplicitTruncation
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticClosureMass
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound

public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

theorem _root_.HordijkSteelThreshold.SplitModel.escape_eq' (M : SplitModel) {K : ℕ} (hK : 2 ≤ K) (a : I) :
    infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf M.g ω) w} =
      M.μ _ a (M.esc $ K-2) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hK
  exact M.escape_eq K a

end RAFCriticalWindowQuantitative
