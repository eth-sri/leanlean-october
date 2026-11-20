module

public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.FK.FreeBoxTranslation
public import PottsDiscontinuity.FK.WiredLimitTranslation
public import PottsDiscontinuity.Infra.CylinderUniqueness

/-!
# Translation invariance on the exact frozen carrier

Uniqueness of the frozen cylinder characterization transfers the invariance of
the canonical free and wired limits to every measure satisfying that
characterization.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

theorem isRCInfiniteVolumeLimit_interior_translation_invariant
    {θ : Parameters} {i : Fin 2} {μ : Measure LatticeConfiguration}
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ := by
  fin_cases i
  · let ν := Classical.choose (freeBoxLimit_existsUnique θ)
    have hν := (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
    have heq := rc_limit_unique hμ
      (isRCInfiniteVolumeLimit_of_freeBox_tendsto hν)
    rw [heq]
    exact congrArg ProbabilityMeasure.toMeasure
      (Internal.freeBoxLimit_translation_invariant θ a)
  · let ν := Classical.choose (wiredBoxLimit_existsUnique θ)
    have hν := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
    have heq := rc_limit_unique hμ
      (isRCInfiniteVolumeLimit_of_wiredBox_tendsto hν)
    rw [heq]
    exact congrArg ProbabilityMeasure.toMeasure (wiredBoxLimit_translation_invariant θ a)


end

end PottsDiscontinuity.FK
