module

public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.Mixing

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

variable (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
include hμ

theorem infiniteAt_measure_eq_origin
    (x : LatticeVertex) : μ (infiniteAt x) = μ (infiniteAt (0, 0)) := by
  have hpre : (edgeTranslate x) ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  have hmap := congrArg (fun ν : Measure LatticeConfiguration => ν (infiniteAt x))
    (isRCInfiniteVolumeLimit_interior_translation_invariant hμ x)
  rw [Measure.map_apply (edgeTranslate_measurable x) (measurableSet_infiniteAt x), hpre] at hmap
  exact hmap.symm

/-- Countable union and translation invariance identify positivity of the
existence event with positivity at the origin; uniqueness is not needed. -/
theorem infiniteCluster_pos_iff_origin_pos :
    0 < μ infiniteClusterEvent ↔ 0 < μ (infiniteAt (0, 0)) := by
  constructor
  · intro hpos
    by_contra hn
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hn)
    have hzero : μ infiniteClusterEvent = 0 := by
      rw [infiniteClusterEvent_eq_iUnion]
      apply measure_iUnion_null
      intro x
      rw [infiniteAt_measure_eq_origin θ i μ hμ x, hz]
    exact hpos.ne' hzero
  · intro hpos
    exact hpos.trans_le (measure_mono (by
      intro ω hω
      exact ⟨(0, 0), hω⟩))

end PottsDiscontinuity.RCInfinite
