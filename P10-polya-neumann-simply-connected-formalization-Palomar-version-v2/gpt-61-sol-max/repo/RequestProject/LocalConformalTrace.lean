module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

def localConformalDiskH1Trace {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk)) :
    NeumannH1 (F '' unitDisk) →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (localConformalH1Pullback hR F hFs hL)

def localConformalDiskHalfTrace {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk)) :
    NeumannH1 (F '' unitDisk) →L[ℂ] L2Z :=
  diskHalfTrace.comp (localConformalH1Pullback hR F hFs hL)

@[simp] theorem localConformalDiskHalfTrace_apply  hR F
    (hFs : RealSmoothOnBall F R)
    hL
    u n :
    localConformalDiskHalfTrace hR F hFs hL u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) n :=
  diskHalfTrace_apply _ n

section
variable {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hb : Bornology.IsBounded (F '' unitDisk)) (hL : IsLipschitzDomain (F '' unitDisk)) (hhol : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {C } (hC : DiskInverseJacobianBound F C)
include R hR F hFs hb hL hhol hinj C hC

theorem localConformalDiskH1Trace_smooth_ae
    f :
    (localConformalDiskH1Trace hR F hFs hL (smoothTraceH1 (F '' unitDisk) f) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] fun θ => f (F (unitCircleMap θ)) := by
  change (diskH1Trace (localConformalH1Pullback hR F hFs hL
    (smoothTraceH1 (F '' unitDisk) f))) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f]
  have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (smoothDiskCompositionLin hR F hFs f)
  filter_upwards [h] with θ hθ
  rw [diskH1Trace, hθ]
  exact smoothDiskCompositionLin_eq_closedDisk hR F hFs f
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ))

theorem localConformalDiskH1Trace_eq_reparam
     (hγ : IsBoundaryParam (F '' unitDisk) γ)
      (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ)) :
    h1ReparamBoundaryTrace hL hγ hτ = localConformalDiskH1Trace hR F hFs hL := by
  apply h1ReparamBoundaryTrace_unique hb hL hγ hτ
  intro f
  apply Lp.ext
  have h := localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f
  have h' : (smoothReparamBoundaryLin hγ hτ f : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] fun θ => f (γ (τ θ)) :=
    (smoothReparamBoundary_memLp hγ hτ f).coeFn_toLp
  filter_upwards [h, h'] with θ hθ hθ'
  rw [hθ, hθ', hcoord]

end


end PolyaNeumann

end
