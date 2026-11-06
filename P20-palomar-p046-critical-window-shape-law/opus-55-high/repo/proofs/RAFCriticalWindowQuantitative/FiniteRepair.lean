module

public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.SplitModel

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

/-- Coordinate maps preserving every split prefix, in both directions. -/
def PrefixIndex (g : List Bool × ℕ → List Bool × ℕ) : Prop :=
  ∀ B z, g z ∈ splitPrefixCoordinates B ↔ z ∈ splitPrefixCoordinates B

variable {g : List Bool × ℕ → List Bool × ℕ}

end RAFCriticalWindowQuantitative
