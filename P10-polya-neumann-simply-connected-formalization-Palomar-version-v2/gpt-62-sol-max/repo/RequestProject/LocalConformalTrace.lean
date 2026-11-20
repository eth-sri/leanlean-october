module

public import RequestProject.LocalConformalPullback
public import RequestProject.DiskHalfTrace
public import RequestProject.TraceReparam

/-!
# Physical half-order traces in local conformal coordinates

The disk estimates and the proved H¹ pullback construct the half-order
trace for a given local smooth conformal coordinate map. Its ordinary
boundary values agree with `f(F(exp(iθ)))` on all smooth restrictions.
When these coordinates are a C¹ reparametrization of the physical
boundary parameter, uniqueness identifies the constructed ordinary trace
with the previously constructed reparametrized physical trace.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff Topology

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
include R hR F hFs hL

def localConformalDiskH1Trace  :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (localConformalH1Pullback hR F hFs hL)

def localConformalDiskHalfTrace  :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskHalfTrace.comp (localConformalH1Pullback hR F hFs hL)

@[simp] theorem localConformalDiskHalfTrace_apply 
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) (n : ℤ) :
    localConformalDiskHalfTrace hR F hFs hL u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) n :=
  diskHalfTrace_apply _ n

end

abbrev ConformalDiskCoordinates.trace {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    NeumannH1 (F '' ball 0 1) →L[ℂ] BoundaryL2 :=
  localConformalDiskH1Trace coords.one_lt_radius F coords.smooth coords.lipschitz

abbrev ConformalDiskCoordinates.halfTrace {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    NeumannH1 (F '' ball 0 1) →L[ℂ] L2Z :=
  localConformalDiskHalfTrace coords.one_lt_radius F coords.smooth coords.lipschitz

section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

theorem localConformalDiskH1Trace_smooth_ae 
    (f : smoothTraceTests) :
    (coords.trace (smoothTraceH1 (F '' ball 0 1) f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (F (circleMap 0 1 θ)) := by
  change (diskH1Trace (coords.pullback
    (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)) : ℝ → ℂ) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth coords.one_lt_radius F coords.smooth coords.bounded coords.lipschitz coords.holomorphic coords.injOn coords.lower f]
  have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (smoothDiskCompositionLin coords.one_lt_radius F coords.smooth f)
  filter_upwards [h] with θ hθ
  rw [diskH1Trace, hθ]
  exact smoothDiskCompositionLin_eq_closedDisk coords.one_lt_radius F coords.smooth f
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

theorem localConformalDiskH1Trace_eq_reparam 
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ)) :
    h1ReparamBoundaryTrace coords.lipschitz hγ hτ = coords.trace := by
  apply h1ReparamBoundaryTrace_unique coords.bounded coords.lipschitz hγ hτ
  intro f
  apply Lp.ext
  have h := localConformalDiskH1Trace_smooth_ae coords f
  have h' : (smoothReparamBoundaryLin hγ hτ f : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (γ (τ θ)) :=
    (smoothBoundary_memLp (hγ.continuous.comp hτ.continuous) f).coeFn_toLp
  filter_upwards [h, h'] with θ hθ hθ'
  simp_all

end

end PolyaNeumann

end
