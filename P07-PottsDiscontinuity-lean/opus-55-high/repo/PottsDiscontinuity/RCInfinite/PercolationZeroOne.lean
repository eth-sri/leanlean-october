module

public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.ErgodicLimits

public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

section
variable (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ)
include p q hq i hμ
theorem infiniteAt_measure_eq_origin
    (x : LatticeVertex) : μ (infiniteAt x) = μ (infiniteAt (0, 0)) := by
  have hpre : (edgeTranslate x) ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  have hmap := congrArg (fun ν : Measure LatticeConfiguration => ν (infiniteAt x))
    (translation_invariant p q hq i μ hμ x)
  rw [Measure.map_apply (edgeTranslate_measurable x) (measurableSet_infiniteAt x), hpre] at hmap
  simp_all

/-- Countable union and translation invariance identify positivity of the
existence event with positivity at the origin; uniqueness is not needed. -/
theorem infiniteCluster_pos_iff_origin_pos
     :
    0 < μ infiniteClusterEvent ↔ 0 < μ (infiniteAt (0, 0)) := by
  constructor
  · intro hpos
    by_contra hn
    have hz : μ (infiniteAt (0, 0)) = 0 := by simp_all
    have hzero : μ infiniteClusterEvent = 0 := by
      rw [infiniteClusterEvent_eq_iUnion]
      apply measure_iUnion_null
      grind [infiniteAt_measure_eq_origin]
    simp_all
  · intro hpos
    exact hpos.trans_le (measure_mono (by
      intro ω hω
      exact ⟨(0, 0), hω⟩))

theorem infiniteCluster_zero_one
     :
    μ infiniteClusterEvent = 0 ∨ μ infiniteClusterEvent = 1 := by
  have : IsProbabilityMeasure μ := hμ.1
  exact (isRCInfiniteVolumeLimit_edge_ergodic p q hq i μ hμ).zero_one
    measurableSet_infiniteClusterEvent infiniteClusterEvent_invariant
end

end PottsDiscontinuity.RCInfinite
