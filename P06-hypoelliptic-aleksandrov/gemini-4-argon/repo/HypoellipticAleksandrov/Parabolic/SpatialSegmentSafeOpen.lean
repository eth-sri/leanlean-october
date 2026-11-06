module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Compactness.Compact

/-!
# Spatial-segment-safe carriers

This module defines the maximal carrier whose directed spatial-shift segments
remain in a prescribed set, and proves that this carrier is open when the
prescribed set is open.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set
open scoped Convex

/- The points whose full directed segment to the given spatial shift remains
inside `U`. -/
noncomputable def spatialSegmentSafeSet {d }
    (U : Set (TimeVelocity d)) (k : Fin d) (h : ℝ) :
    Set (TimeVelocity d) :=
  {z | [z -[ℝ] spatialShift k h z] ⊆ U}

/- Membership in the spatial-segment-safe carrier is its defining segment
containment condition. -/
@[simp] theorem mem_spatialSegmentSafeSet_iff {d }
    (U : Set (TimeVelocity d)) (k : Fin d) (h : ℝ)
    (z : TimeVelocity d) :
    z ∈ spatialSegmentSafeSet U k h ↔
      [z -[ℝ] spatialShift k h z] ⊆ U := Iff.rfl

/- The maximal spatial-segment-safe carrier of an open set is open. -/
end HypoellipticAleksandrov.Parabolic
