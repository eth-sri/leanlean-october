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

variable {d : ℕ} (U : HypoellipticAleksandrov.Parabolic.Region d)

variable (k : Fin d) (h : ℝ)

/-- The points whose full directed segment to the given spatial shift remains
inside `U`. -/
noncomputable def spatialSegmentSafeSet   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  {z | [z -[ℝ] spatialShift k h z] ⊆ U}

/-- Membership in the spatial-segment-safe carrier is its defining segment
containment condition. -/
@[simp] theorem mem_spatialSegmentSafeSet_iff
    (z : TimeVelocity d) :
    z ∈ spatialSegmentSafeSet U k h ↔
      [z -[ℝ] spatialShift k h z] ⊆ U := Iff.rfl

/-- The maximal spatial-segment-safe carrier of an open set is open. -/
theorem isOpen_spatialSegmentSafeSet  (hU : IsOpen U)
    (k : Fin d) (h : ℝ) :
    IsOpen (spatialSegmentSafeSet U k h) := by
  let F : TimeVelocity d × ℝ → TimeVelocity d := fun p =>
    p.1 + p.2 • (spatialShift k h p.1 - p.1)
  have hshift : Continuous (spatialShift k h) := by
    change Continuous (fun z : TimeVelocity d =>
      z + (0, h • PDE.basisVec k))
    exact continuous_id.add continuous_const

  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hzseg : [z -[ℝ] spatialShift k h z] ⊆ U := hz


  obtain ⟨(u : HypoellipticAleksandrov.Parabolic.Region d), (v : Set ℝ), hu, hv, hzu, hIv, huv⟩ :=
    generalized_tube_lemma

       (isCompact_singleton ) isCompact_Icc (hU.preimage (show Continuous F by
           exact continuous_fst.add
             (continuous_snd.smul ((hshift.comp continuous_fst).sub continuous_fst)))) (by
           rintro ⟨z', s⟩ ⟨hz', hs⟩
           simp only [mem_singleton_iff] at hz'
           subst z'
           rw [segment_eq_image' ℝ z (spatialShift k h z)] at hzseg
           exact hzseg (mem_image_of_mem _ hs))
  refine Filter.mem_of_superset (hu.mem_nhds (hzu (mem_singleton z))) ?_
  intro z' hz'

  change [z' -[ℝ] spatialShift k h z'] ⊆ U
  rw [segment_eq_image' ℝ z' (spatialShift k h z')]
  intro w hwmem
  rcases hwmem with ⟨(s : ℝ), hs, hw⟩
  rw [← hw]

  exact huv (show (z', s) ∈ u ×ˢ v from ⟨hz', @hIv s hs⟩)

end HypoellipticAleksandrov.Parabolic
