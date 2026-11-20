module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalReducedBoundaryBound
public import RequestProject.LocalConformalHerglotzBoundaryTransfer
public import RequestProject.PlanarNotation

/-! The Herglotz boundary estimate for actual supplied conformal coordinates.
The reduced form, physical quadratic form, finite conditions and normalization
are derived by the imported results. Construction of these coordinates from
the original smooth-domain hypotheses remains a separate step. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace PolyaNeumann
open Set Metric

section Coordinates

theorem exists_localConformal_original_herglotz_boundary_bound (Φ : DiskCoordinates) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) (Ws : ℝ → TransportPath)
    (hWs : ∀ E, IsTransport Φ.boundary E (Ws E)) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutVector (Ws E₀) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) →
      ∀ W : TransportPath, IsTransport γ E W →
        ∃ ℓ : (ℝ → ℂ) →ₗ[ℂ] (Fin (originalNeumannMultiplicity Φ.domain E₀) → ℂ),
          ∀ a, IsDirDensity a → ℓ a = 0 →
            -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm W γ E a := exists_uniform_originalHerglotz_bound_of_normalized Φ hγ hτ hcoord hΓLip Ws hWs E₀ hcut
    (exists_localConformal_normalized_reduced_boundary_bound Φ hγ hτ hcoord hΓLip Ws hWs hE₀ hcut)

theorem exists_localConformal_original_herglotz_boundary_bound_of_multiplicity (Φ : DiskCoordinates) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) (Ws : ℝ → TransportPath)
    (hWs : ∀ E, IsTransport Φ.boundary E (Ws E)) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutVector (Ws E₀) ≠ 0) (m : ℕ)
    (hm : {j | neumannEigenvalue Φ.domain j = ENNReal.ofReal E₀}.encard = m) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) →
      ∀ W : TransportPath, IsTransport γ E W →
        ∃ ℓ : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → ℓ a = 0 →
          -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
            herglotzForm W γ E a := by
  have hmult : originalNeumannMultiplicity Φ.domain E₀ = m := by
    unfold originalNeumannMultiplicity
    rw [hm]
    exact ENat.toNat_coe m
  have hbase := exists_localConformal_original_herglotz_boundary_bound Φ hγ hτ hcoord hΓLip Ws hWs hE₀ hcut
  subst m
  exact hbase

end Coordinates
end PolyaNeumann
end
