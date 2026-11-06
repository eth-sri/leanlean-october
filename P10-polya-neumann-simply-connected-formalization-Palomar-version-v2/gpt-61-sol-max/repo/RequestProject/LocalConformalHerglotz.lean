module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalBoundaryLoad
public import RequestProject.NeumannHerglotzBoundary

/-!
# Actual Herglotz waves in conformal weak coordinates

The physical conormal load is the genuine ordinary-coordinate boundary L²
trace, transformed with its proved Jacobian factor. The normalized variational
solution is identified with the actual interior Herglotz wave by its Green
identity and uniqueness at a nonresonant physical Neumann energy.
-/

public section

open scoped ContDiff



namespace PolyaNeumann

open Set Metric

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

include hhol hinj hC hcoord

/-- The actual physical Herglotz Green equation in normalized weak coordinates. -/
theorem localConformalHerglotz_isNormalizedNeumannSolution
     (hE : 0 ≤ E)  (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 hb ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE)

end PolyaNeumann
