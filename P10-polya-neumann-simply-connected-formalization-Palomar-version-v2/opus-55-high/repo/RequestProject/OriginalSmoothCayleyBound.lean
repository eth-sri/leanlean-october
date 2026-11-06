module

public import RequestProject.RiemannMappingSmoothCollar
public import RequestProject.LocalConformalBoundaryParamSync
public import RequestProject.LocalConformalSuppliedHerglotzBound
public import RequestProject.BoundaryOrigin
public import RequestProject.CayleyChosenOrigin
public import RequestProject.Reparam

/-!
# The original smooth-domain Cayley bound at a chosen physical origin

The origin is chosen on the supplied physical boundary parameter.  The genuine
smooth conformal coordinates are then synchronized with this shifted physical
curve.  Their endpoint-preserving arclength lift transfers the nonzero cut to
the conformal transport, so the actual supplied-coordinate Herglotz estimate
has exactly the chosen-origin form required by the Cayley rank transfer.

The intermediate monodromy nontriviality input is the genuine fixed-space
consequence proved before the smooth-domain argument in `Main`.  This module
does not import `Main`, and its spectral restriction and multiplicity are the
original ones.  This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Real

/-- The unchanged uniform Cayley rank estimate under the original bounded
smooth simply-connected domain assumptions, using the independently proved
nontriviality of the original boundary monodromy at the center energy. -/
theorem uniform_cayley_rank_bound_of_original_smooth_domain
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E₀ : ℝ) (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = m)
    (hU₀ : monodromyAt γ E₀ ≠ 1) :
    ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      CayleyRankBound (monodromyAt γ E) A m := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hWs  := fun E =>
    Classical.choose_spec (transport_exists_of_lipschitz γ hKγ E)
  obtain ⟨t, ht, ε, hε, _hεE, hcut⟩ :=
    exists_boundary_origin_of_boundaryParam hγ hWs hE₀ (by
    simp_all [monodromyAt_eq hKγ (hWs E₀)])
  let γt  := fun θ => γ (θ + t)
  have hγt  := hγ.shift t

  obtain ⟨R, C, K, F, e, hR, _hCpos, _hKpos, hFs, hhol, _hinj, himage,
    _hnz, hC, hK, he, hsource, hes, _hclosed, _hsphere⟩ :=
    exists_smoothConformal_coordinates Ω hb hS hsc
  obtain ⟨φ, _hφ, c, L, himageφ, _hclosedφ, hFsφ, hbφ, hLφ, hholφ,
    hinjφ, hCφ, hKφ, heφ, hsourceφ, hesφ, hγtφ, hτ, _hτper, hcoord,
    hΓLip, _horigin⟩ :=
    exists_localConformal_original_boundary_coordinates hR F hFs (by
    simp_all) (by
    rw [himage]
    exact hS.isLipschitzDomain) hhol
      hC hK e he hsource hes (by
    rw [himage]
    assumption)
  let τ  :=
    localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
  let Γ  := physicalCircleTrace (localConformalRotate F φ)
  have hτ'  := hτ
  have hcomp : Γ = γt ∘ τ := by
    funext θ
    exact hcoord θ
  let WΓ  := fun E =>
    Classical.choose (transport_exists_of_lipschitz Γ hΓLip E)
  obtain ⟨Kγt, hKγt⟩ := hγt.lipschitz
  obtain ⟨Wt, hWt⟩ := transport_exists_of_lipschitz γt hKγt E₀
  have hcut_t  :=
    hcut E₀ ⟨by linarith, by linarith⟩ Wt hWt
  obtain ⟨Kτ, hKτ⟩ := hτ'.lipschitz
  have hWΓcomp : IsTransport (γt ∘ τ) E₀ (WΓ E₀) := by
    grind
  have hmono  :=
    monodromy_comp hKγt hτ'.monotone hKτ hτ'.zero hτ'.endpoint hWt hWΓcomp
  obtain ⟨A, δ, _hA, hδ, hbound⟩ :=
    exists_localConformal_original_herglotz_boundary_bound_of_multiplicity
      hR (localConformalRotate F φ) hFsφ hbφ hLφ hholφ
      (hinjφ.mono ball_subset_closedBall) hCφ hKφ
      (localConformalRotatePartialHomeomorph e φ) heφ hsourceφ hesφ
      hγtφ hτ hcoord hΓLip WΓ (fun E =>
    Classical.choose_spec (transport_exists_of_lipschitz Γ hΓLip E)) hE₀ (by
    have hcut_eq : cutC (WΓ E₀ (2 * π)) (basisVec 0) =
        cutC (Wt (2 * π)) (basisVec 0) := by
      change monodromy (WΓ E₀) (basisVec 0) - basisVec 0 =
        monodromy Wt (basisVec 0) - basisVec 0
      simp_all
    simp_all) m (by
    simp_all)
  refine uniform_cayley_rank_bound_of_chosen_origin hKγ hγ.periodic E₀ m
    (fun E => ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) ?_
  refine ⟨t, ht, A, δ, hδ, ?_⟩
  simp_all

end PolyaNeumann

end
