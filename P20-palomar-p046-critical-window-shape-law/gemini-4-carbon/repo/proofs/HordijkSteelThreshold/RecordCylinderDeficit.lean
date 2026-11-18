module

public import proofs.HordijkSteelThreshold.RecordTargetProbability
public import proofs.HordijkSteelThreshold.RecordPrefixAtoms

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory unitInterval
open scoped ENNReal

theorem measurableSet_of_splitPrefixDetermined (P : Finset (List Bool × ℕ))
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  rw [he]
  have hm : Measurable (fun ω : SplitField => e (fun z : P => ω z.val)) :=
    (measurable_of_finite e).comp (Measurable.of_eval (fun z => measurable_pi_apply z.val))
  simpa using (MeasurableSet.singleton True).preimage hm

end HordijkSteelThreshold
