
import proofs.HordijkSteelThreshold.RecordCylinderDeficit


namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete MeasureTheory unitInterval

/-- Reindexings which preserve products and finite prefixes. -/
structure PrefixIndex where
  index : (List Bool × ℕ) → (List Bool × ℕ)
  product : ∀ z, (index z).1 = z.1
  preserves : ∀ {B z}, z ∈ splitPrefixCoordinates B → index z ∈ splitPrefixCoordinates B

def splitPrefixIndex : PrefixIndex := ⟨id,fun _ => rfl,fun h => h⟩

def indexedField (f : PrefixIndex) (ω : SplitField)  :=
  currySplitField (ω ∘ f.index)


end RAFCriticalWindowQuantitative
