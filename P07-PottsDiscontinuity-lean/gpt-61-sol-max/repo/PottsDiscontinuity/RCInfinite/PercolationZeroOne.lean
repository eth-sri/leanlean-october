module
public import Mathlib

public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.ErgodicLimits

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

section

variable (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ)
include hq hμ

theorem infiniteAt_measure_eq_origin
    
    (x : LatticeVertex) : μ (infiniteAt x) = μ (infiniteAt (0, 0)) := by
  have hpre :  edgeTranslate x  ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  have hmap := congrArg (fun ν  => ν (infiniteAt x))
    (translation_invariant p q hq i μ hμ x)
  rw [Measure.map_apply (edgeTranslate_measurable x) (measurableSet_infiniteAt x), hpre] at hmap
  exact hmap.symm

/-- Countable union and translation invariance identify positivity of the
existence event with positivity at the origin; uniqueness is not needed. -/
theorem infiniteCluster_pos_iff_origin_pos
     :
    0 < μ infiniteClusterEvent ↔ 0 < μ (infiniteAt (0, 0)) := by
  constructor
  · intro hpos
    by_contra hn
    
    
    exact hpos.ne' (by
                      rw [infiniteClusterEvent_eq_iUnion]
                      apply measure_iUnion_null
                      intro x
                      rw [infiniteAt_measure_eq_origin p q hq i μ hμ x,  nonpos_iff_eq_zero.mp (not_lt.mp hn) ])
  · intro hpos
    exact hpos.trans_le (measure_mono  fun ω hω => ⟨(0, 0), hω⟩ )

theorem infiniteCluster_zero_one
     :
    μ infiniteClusterEvent = 0 ∨ μ infiniteClusterEvent = 1 := have this := hμ.left;
                                                               IsEdgeTranslationErgodic.zero_one (isRCInfiniteVolumeLimit_edge_ergodic p q hq i μ hμ)
                                                                 measurableSet_infiniteClusterEvent infiniteClusterEvent_invariant

end

end PottsDiscontinuity.RCInfinite
