module

public import proofs.HordijkSteelThreshold.RecordTargetProbability
public import proofs.HordijkSteelThreshold.RecordPrefixAtoms

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

theorem measurableSet_of_splitPrefixDetermined (P : Finset (List Bool × ℕ))
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
  obtain ⟨e, rfl⟩ := split_prefix_event_representation P E hE
  exact (Set.toFinite {η : P → Prop | e η}).measurableSet.preimage
    (Measurable.of_eval fun z => measurable_pi_apply z.val)

end HordijkSteelThreshold
