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

variable {R : ℝ} {C : ℝ}

local notation "Φ0" => ball 0 1

def localConformalDiskH1Trace  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hL : IsLipschitzDomain (F '' Φ0)) :
    NeumannH1 (F '' Φ0) →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (localConformalH1Pullback hR F hFs hL)

def localConformalDiskHalfTrace  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hL : IsLipschitzDomain (F '' Φ0)) :
    NeumannH1 (F '' Φ0) →L[ℂ] L2Z :=
  diskHalfTrace.comp (localConformalH1Pullback hR F hFs hL)

@[simp] theorem localConformalDiskHalfTrace_apply  (hR : 1 < R) F
    hFs
    hL
    u n :
    localConformalDiskHalfTrace hR F hFs hL u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) n :=
  diskHalfTrace_apply _ n

theorem localConformalDiskH1Trace_smooth_ae  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' Φ0))
    hL
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0)) 
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    f :
    (localConformalDiskH1Trace hR F hFs hL (smoothTraceH1 (F '' Φ0) f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ => f (F (circleMap 0 1 θ)) := by
  change (diskH1Trace (localConformalH1Pullback hR F hFs hL
    (smoothTraceH1 (F '' Φ0) f)) : ℝ → ℂ) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f]
  filter_upwards [h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam (smoothDiskCompositionLin hR F hFs f)] with θ hθ
  rw [diskH1Trace, hθ]
  exact smoothDiskCompositionLin_eq_closedDisk hR F hFs f
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

theorem localConformalDiskH1Trace_eq_reparam  (hR : 1 < R) (F : ℂ → ℂ)
    hFs
    (hb : Bornology.IsBounded (F '' Φ0))
    hL
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0)) 
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' Φ0) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ)) :
    h1ReparamBoundaryTrace hL hγ hτ = localConformalDiskH1Trace hR F hFs hL := by
  apply h1ReparamBoundaryTrace_unique hb hL hγ hτ
  intro f
  apply Lp.ext
  have h := localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f
  have h' : smoothReparamBoundaryLin hγ hτ f
      =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ => f (γ (τ θ)) :=
    (smoothReparamBoundary_memLp hγ hτ f).coeFn_toLp
  filter_upwards [h, h'] with θ hθ hθ'
  rw [hθ, hθ', hcoord]

end PolyaNeumann

end
