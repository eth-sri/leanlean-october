module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalReducedBoundaryBound
public import RequestProject.LocalConformalHerglotzBoundaryTransfer

/-! The Herglotz boundary estimate for actual supplied conformal coordinates.
The reduced form, physical quadratic form, finite conditions and normalization
are derived by the imported results. Construction of these coordinates from
the original smooth-domain hypotheses remains a separate step. -/

@[expose] public section

open scoped ContDiff
noncomputable section
namespace PolyaNeumann
open Set Metric

section Coordinates

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

local notation "ΩF" => F '' unitDisk
local notation "ΓF" => physicalCircleTrace F

section
include hR hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord

theorem exists_localConformal_original_herglotz_boundary_bound
     (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → ComplexEnd Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
     (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ circlePeriod) (basisVec 0) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ W : ℝ → ComplexEnd Ell2, IsTransport γ E W →
        ∃ ℓ : (ComplexCurve) →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
          ∀ a, IsDirDensity a → ℓ a = 0 →
            -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm W γ E a := exists_uniform_originalHerglotz_bound_of_normalized hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip Ws hWs E₀ hcut
    (exists_localConformal_normalized_reduced_boundary_bound hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord hΓLip Ws hWs hE₀ hcut)

theorem exists_localConformal_original_herglotz_boundary_bound_of_multiplicity
     (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → ComplexEnd Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
     (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ circlePeriod) (basisVec 0) ≠ 0)
    (m : ℕ) (hm : {j | neumannEigenvalue ΩF j = ENNReal.ofReal E₀}.encard = m) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ W : ℝ → ComplexEnd Ell2, IsTransport γ E W →
        ∃ ℓ : (ComplexCurve) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → ℓ a = 0 →
          -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
            herglotzForm W γ E a := by
  have hmult : originalNeumannMultiplicity ΩF E₀ = m := by
    simp_all [originalNeumannMultiplicity]
  have hbase := exists_localConformal_original_herglotz_boundary_bound hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hγ hτ hcoord hΓLip Ws hWs hE₀ hcut
  subst m
  exact hbase

end


end Coordinates
end PolyaNeumann