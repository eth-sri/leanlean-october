module

public import RequestProject.DiskCoordinates

public import RequestProject.RiemannMappingSmoothCollar
public import RequestProject.LocalConformalBoundaryParamSync
public import RequestProject.LocalConformalSuppliedHerglotzBound
public import RequestProject.BoundaryOrigin
public import RequestProject.CayleyChosenOrigin
public import RequestProject.Reparam
public import RequestProject.PlanarNotation

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
  choose Ws hWs using transport_exists_of_lipschitz γ hKγ
  have hU : monodromy (Ws E₀) ≠ 1 := by
    simpa only [monodromyAt_eq hKγ (hWs E₀)] using hU₀
  obtain ⟨t, ht, ε, hε, _hεE, hcut⟩ :=
    exists_boundary_origin_of_boundaryParam hγ hWs hE₀ hU
  let γt  := fun θ => γ (θ + t)
  have hγt  := hγ.shift t

  obtain ⟨Φ, himage⟩ := exists_smoothConformal_coordinates Ω hb hS hsc
  obtain ⟨φ, _, c, hτ, heq⟩ := Φ.boundaryParam_sync (himage.symm ▸ hγt)
  let Ψ := Φ.rotate φ
  have hΨ : Ψ.domain = Ω := (Φ.rotate_domain φ).trans himage
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  obtain ⟨Kγt, hKγt⟩ := hγt.lipschitz
  have hΓLip : LipschitzWith (Kγt * Kτ) Ψ.boundary := heq.symm ▸ hKγt.comp hKτ
  choose WΓ hWΓ using transport_exists_of_lipschitz Ψ.boundary hΓLip
  obtain ⟨Wt, hWt⟩ := transport_exists_of_lipschitz γt hKγt E₀
  have hcut_t := hcut E₀ ⟨by linarith, by linarith⟩ Wt hWt
  have hWt' := hWΓ E₀
  change IsTransport (Φ.rotate φ).boundary E₀ (WΓ E₀) at hWt'
  rw [heq] at hWt'
  have hmono := monodromy_comp hKγt hτ.monotone hKτ hτ.zero hτ.endpoint hWt hWt'
  have hcutΓ : cutVector (WΓ E₀) ≠ 0 := by
    change monodromy (WΓ E₀) (basisVec 0) - basisVec 0 ≠ 0
    rwa [hmono]
  obtain ⟨A, δ, _, hδ, hbound⟩ :=
    exists_localConformal_original_herglotz_boundary_bound_of_multiplicity Ψ (γ := γt)
      (hΨ.symm ▸ hγt) hτ (fun θ => congrFun heq θ) hΓLip WΓ hWΓ hE₀ hcutΓ m (hΨ.symm ▸ hm)
  refine uniform_cayley_rank_bound_of_chosen_origin hKγ hγ.periodic E₀ m
    (fun E => ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) ⟨t, ht, A, δ, hδ, ?_⟩
  intro E hE hnear hnr W hW
  exact hbound E hE hnear (hΨ.symm ▸ hnr) W hW

end PolyaNeumann
end
