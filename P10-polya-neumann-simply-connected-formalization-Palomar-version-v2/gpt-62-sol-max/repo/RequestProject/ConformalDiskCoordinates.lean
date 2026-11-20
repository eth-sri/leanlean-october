module

public import RequestProject.Defs
public import RequestProject.RiemannMappingInterior
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology

/-- Smooth conformal disk coordinates with a smooth inverse near the closed disk.
The two bounds control the Jacobian from below and the differential from above. -/
structure ConformalDiskCoordinates (F : ℂ → ℂ) where
  radius : ℝ
  inverseBound : ℝ
  derivativeBound : ℝ
  one_lt_radius : 1 < radius
  bounded : Bornology.IsBounded (F '' ball 0 1)
  lipschitz : IsLipschitzDomain (F '' ball 0 1)
  holomorphic_collar : DifferentiableOn ℂ F (ball 0 radius)
  injOn_collar : InjOn F (ball 0 radius)
  lower : ∀ z ∈ ball 0 1, 1 ≤ inverseBound * ‖deriv F z‖ ^ 2
  upper_deriv : ∀ z ∈ ball 0 1, ‖deriv F z‖ ≤ derivativeBound

namespace ConformalDiskCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

lemma smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 coords.radius) :=
  (coords.holomorphic_collar.contDiffOn isOpen_ball).restrict_scalars ℝ

lemma holomorphic :
    DifferentiableOn ℂ F (ball 0 1) :=
  coords.holomorphic_collar.mono (ball_subset_ball coords.one_lt_radius.le)

lemma injOn_closed :
    InjOn F (closedBall 0 1) :=
  coords.injOn_collar.mono (closedBall_subset_ball coords.one_lt_radius)

lemma injOn :
    InjOn F (ball 0 1) := coords.injOn_closed.mono ball_subset_closedBall

lemma differentiableAt_closed
    {z : ℂ} (hz : z ∈ closedBall 0 1) : DifferentiableAt ℂ F z :=
  coords.holomorphic_collar.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball coords.one_lt_radius hz))

lemma upper (z : ℂ) (hz : z ∈ ball 0 1) : ‖fderiv ℝ F z 1‖ ≤ coords.derivativeBound := by
  rw [(coords.holomorphic.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact coords.upper_deriv z hz

lemma deriv_ne_zero {z : ℂ} (hz : z ∈ ball 0 coords.radius) : deriv F z ≠ 0 :=
  RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball coords.holomorphic_collar coords.injOn_collar hz

lemma deriv_ne_zero_closed {z : ℂ} (hz : z ∈ closedBall 0 1) : deriv F z ≠ 0 :=
  coords.deriv_ne_zero (closedBall_subset_ball coords.one_lt_radius hz)

def model : OpenPartialHomeomorph ℂ ℂ := by
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict
    (coords.injOn_collar.toPartialEquiv F _) coords.holomorphic_collar.continuousOn ?_ isOpen_ball
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  change 𝓝 (F x) ≤ map (F ∘ Subtype.val) (𝓝 x)
  rw [← map_map, map_nhds_subtype_val]
  change 𝓝 (F x) ≤ map F (𝓝[ball 0 coords.radius] x.val)
  have hx := x.property
  rw [isOpen_ball.nhdsWithin_eq hx]
  exact ((coords.holomorphic_collar.analyticOnNhd isOpen_ball x hx).hasStrictDerivAt
    |>.map_nhds_eq (coords.deriv_ne_zero hx)).ge

lemma model_eq : (coords.model : ℂ → ℂ) = F := rfl

lemma source : closedBall 0 1 ⊆ coords.model.source := closedBall_subset_ball coords.one_lt_radius

lemma smooth_inv : ContDiffOn ℝ (⊤ : ℕ∞) coords.model.symm coords.model.target := by
  have h : DifferentiableOn ℂ coords.model.symm coords.model.target := by
    intro y hy
    have hx := coords.model.symm.mapsTo hy
    exact (coords.model.hasDerivAt_symm hy (coords.deriv_ne_zero hx)
      (coords.holomorphic_collar.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
      ).differentiableAt.differentiableWithinAt
  exact (h.contDiffOn coords.model.open_target).restrict_scalars ℝ

end ConformalDiskCoordinates

end PolyaNeumann
