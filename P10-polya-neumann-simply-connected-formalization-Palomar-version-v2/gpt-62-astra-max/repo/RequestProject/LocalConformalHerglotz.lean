module

public import RequestProject.LocalConformalBoundaryLoad
public import RequestProject.NeumannHerglotzBoundary

/-!
# Actual Herglotz waves in conformal weak coordinates

The physical conormal load is the genuine ordinary-coordinate boundary L²
trace, transformed with its proved Jacobian factor. The normalized variational
solution is identified with the actual interior Herglotz wave by its Green
identity and uniqueness at a nonresonant physical Neumann energy.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hhol hinj hC hcoord

/-- The actual physical Herglotz Green equation in normalized weak coordinates. -/
theorem localConformalHerglotz_isNormalizedNeumannSolution
    {E : ℝ} (hE : 0 ≤ E) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 hb ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE)

end PolyaNeumann

end
