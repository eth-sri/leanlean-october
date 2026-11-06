module

public import RequestProject.LocalConformalReducedBoundaryBound
public import RequestProject.LocalConformalHerglotzBoundaryTransfer

/-! The Herglotz boundary estimate for actual supplied conformal coordinates.
The reduced form, physical quadratic form, finite conditions and normalization
are derived by the imported results. Construction of these coordinates from
the original smooth-domain hypotheses remains a separate step. -/

@[expose] public section
noncomputable section
open scoped ContDiff

namespace PolyaNeumann
open Set Metric

section Coordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball 0 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball 0 1
local notation "ΓF" => physicalCircleTrace F



include hR hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem exists_localConformal_original_herglotz_boundary_bound_of_multiplicity
     (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
     (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0)
    (m : ℕ) (hm : {j | neumannEigenvalue ΩF j = ENNReal.ofReal E₀}.encard = m) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
        ∃ ℓ : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → ℓ a = 0 →
          -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
            herglotzForm W γ E a := by
  have hmult : originalNeumannMultiplicity ΩF E₀ = m := by
    unfold originalNeumannMultiplicity
    rw [hm]
    exact ENat.toNat_coe m
  subst m
  exact exists_uniform_originalHerglotz_bound_of_normalized hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip Ws hWs E₀ hcut
    (exists_localConformal_normalized_reduced_boundary_bound hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord hΓLip Ws hWs hE₀ hcut)

end Coordinates
end PolyaNeumann
end
