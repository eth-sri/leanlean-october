module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalPullback
public import RequestProject.DiskHalfTrace
public import RequestProject.TraceReparam
public import RequestProject.PlanarNotation

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

variable (Φ : SmoothDiskMap) (hL : IsLipschitzDomain Φ.domain)
include hL

def SmoothDiskMap.pulledBackTrace :
    NeumannH1 Φ.domain →L[ℂ] BoundaryL2 :=
  diskH1Trace.comp (Φ.h1Pullback hL)

def SmoothDiskMap.pulledBackHalfTrace :
    NeumannH1 Φ.domain →L[ℂ] L2Z :=
  diskHalfTrace.comp (Φ.h1Pullback hL)

@[simp] theorem localConformalDiskHalfTrace_apply (u : NeumannH1 Φ.domain) (n : ℤ) :
    Φ.pulledBackHalfTrace hL u n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (Φ.pulledBackTrace hL u) n :=
  diskHalfTrace_apply _ n

end

theorem localConformalDiskH1Trace_smooth_ae (Φ : ConformalDiskMap)
    (f : smoothTraceTests) :
    (Φ.pulledBackTrace Φ.lipschitzDomain (smoothTraceH1 Φ.domain f) : ℝ → ℂ)
      =ᵐ[angleMeasure] fun θ => f (Φ.map (unitCirclePt θ)) := by
  change (diskH1Trace (Φ.h1Pullback Φ.lipschitzDomain
    (smoothTraceH1 Φ.domain f)) : ℝ → ℂ) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth Φ f]
  have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)
  filter_upwards [h] with θ hθ
  rw [diskH1Trace, hθ]
  exact smoothDiskCompositionLin_eq_closedDisk Φ.one_lt_radius Φ.map Φ.smooth f
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

theorem localConformalDiskH1Trace_eq_reparam (Φ : ConformalDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) :
    h1ReparamBoundaryTrace Φ.lipschitzDomain hγ hτ = Φ.pulledBackTrace Φ.lipschitzDomain := by
  apply h1ReparamBoundaryTrace_unique Φ.bounded Φ.lipschitzDomain hγ hτ
  intro f
  apply Lp.ext
  have h := localConformalDiskH1Trace_smooth_ae Φ f
  have h' : (smoothReparamBoundaryLin hγ hτ f : ℝ → ℂ)
      =ᵐ[angleMeasure] fun θ => f (γ (τ θ)) :=
    (smoothReparamBoundary_memLp hγ hτ f).coeFn_toLp
  filter_upwards [h, h'] with θ hθ hθ'
  simp [*]

end PolyaNeumann

end
