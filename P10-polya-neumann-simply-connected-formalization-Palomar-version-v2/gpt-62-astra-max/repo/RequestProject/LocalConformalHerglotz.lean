module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalBoundaryLoad
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open Set Metric

/-- The actual physical Herglotz Green equation in normalized weak coordinates. -/
theorem localConformalHerglotz_isNormalizedNeumannSolution (Φ : ConformalDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E : ℝ} (hE : 0 ≤ E) {a : ℝ → ℂ}
    (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 Φ.bounded ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution Φ hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution Φ.bounded Φ.lipschitzDomain hγ ha hE)

end PolyaNeumann

end
