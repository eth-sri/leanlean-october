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

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hcoord

/-- The actual physical Herglotz Green equation in normalized weak coordinates. -/
theorem localConformalHerglotz_isNormalizedNeumannSolution
    {E : ℝ} (hE : 0 ≤ E) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (coords.halfTrace) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 coords.bounded ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution coords
    hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution coords.bounded coords.lipschitz hγ ha hE)

end PolyaNeumann

end
