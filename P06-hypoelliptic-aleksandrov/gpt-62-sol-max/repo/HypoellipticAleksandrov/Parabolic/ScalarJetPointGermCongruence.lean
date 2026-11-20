module

public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-!
# Scalar jets of equal point germs

This module proves that ambient C² functions agreeing near a point have equal
scalar time, gradient, and ordered Hessian jets at that point.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic
open Filter
open scoped Topology
noncomputable section
open Filter Set

variable {d : ℕ} {f g : TimeVelocity d → ℝ} {z : TimeVelocity d}

section
variable (h : f =ᶠ[nhds z] g)
include h

private theorem timeSlice_congr :
    (fun r => f (r, z.2)) =ᶠ[nhds z.1] (fun r => g (r, z.2)) :=
  h.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto z.1)

private theorem spaceSlice_congr :
    (fun y => f (z.1, y)) =ᶠ[nhds z.2] (fun y => g (z.1, y)) :=
  h.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto z.2)

/-- Functions with the same germ have identical scalar parabolic jets at the point. -/
theorem scalarJet_eqAt_of_eventuallyEq :
    scalarTimeDerivative f z = scalarTimeDerivative g z ∧
    scalarSpatialGradient f z = scalarSpatialGradient g z ∧
    scalarSpatialHessian f z = scalarSpatialHessian g z := by
  have hs := spaceSlice_congr h
  have hg : PDE.classicalGradient (fun y => f (z.1, y)) =ᶠ[nhds z.2]
      PDE.classicalGradient (fun y => g (z.1, y)) := by
    filter_upwards [hs.fderiv (𝕜 := ℝ)] with y hy
    funext i
    simp only [PDE.classicalGradient_apply, hy]
  refine ⟨(timeSlice_congr h).deriv_eq, hg.eq_of_nhds, ?_⟩
  unfold scalarSpatialHessian
  rw [hg.fderiv_eq (𝕜 := ℝ)]

end

variable {s : Set (TimeVelocity d)}

/-- Equality on an open set implies equality of the three jet fields there. -/
theorem scalarJet_eqOn_of_eqOn_open (hs : IsOpen s) (h : EqOn f g s) :
    EqOn (scalarTimeDerivative f) (scalarTimeDerivative g) s ∧
    EqOn (scalarSpatialGradient f) (scalarSpatialGradient g) s ∧
    EqOn (scalarSpatialHessian f) (scalarSpatialHessian g) s := by
  have eqJet (x : TimeVelocity d) (hx : x ∈ s) :=
    scalarJet_eqAt_of_eventuallyEq (h.eventuallyEq_of_mem (hs.mem_nhds hx))
  exact ⟨fun x hx => (eqJet x hx).1, fun x hx => (eqJet x hx).2.1, fun x hx => (eqJet x hx).2.2⟩

/-- `C¹,²` regularity on an open set is invariant under equality there. -/
theorem IsScalarC12On.congr (hg : IsScalarC12On g s) (hs : IsOpen s) (h : EqOn f g s) :
    IsScalarC12On f s := by
  obtain ⟨ht, hgrad, hh⟩ := scalarJet_eqOn_of_eqOn_open hs h
  refine ⟨hg.continuousOn.congr h, ?_, ?_, hg.continuousOn_scalarTimeDerivative.congr ht,
    hg.continuousOn_scalarSpatialGradient.congr hgrad, hg.continuousOn_scalarSpatialHessian.congr hh⟩
  · intro x hx
    exact (hg.timeSlice_differentiableAt hx).congr_of_eventuallyEq
      (timeSlice_congr (h.eventuallyEq_of_mem (hs.mem_nhds hx)))
  · intro x hx
    exact (hg.spatialSlice_contDiffAt hx).congr_of_eventuallyEq
      (spaceSlice_congr (h.eventuallyEq_of_mem (hs.mem_nhds hx)))

end
end HypoellipticAleksandrov.Parabolic
