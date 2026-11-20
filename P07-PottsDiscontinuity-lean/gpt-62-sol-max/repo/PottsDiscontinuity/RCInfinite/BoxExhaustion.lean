module

public import PottsDiscontinuity.FK.LimitTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCInfinite

open PottsDiscontinuity.FK

noncomputable section

/-- The frozen limit is the weak limit along every nested exhaustive box sequence. -/
theorem box_exhaustion (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    WeakBoxLimit (boxMeasure θ i) (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration) := by
  obtain ⟨ν, hν, _⟩ := boxMeasure_existsUnique θ i
  have he : (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration) = ν :=
    ProbabilityMeasure.toMeasure_injective (rc_limit_eq_of_weakBoxLimit hμ hν)
  rwa [he]

end
end PottsDiscontinuity.RCInfinite
