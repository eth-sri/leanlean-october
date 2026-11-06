module

public import RequestProject.CutCorrection
public import RequestProject.Area
public import RequestProject.Observation

/-!
# Choice of a boundary origin (Lemma 6.1)

For every `E₀ > 0` one can choose a boundary origin (a base point `t` of the periodic
boundary curve) and an open interval `I ⊂ (0, ∞)` containing `E₀` such that
`c_E = (V_E^* - I) e₀ ≠ 0` for `E ∈ I`, where `V_E` is the endpoint of the transport
based at `t`.

The proof follows the paper. The transport based at `t` has endpoint `W(t) V W(t)^*`
(`transport_basepoint`). If every rebasing gave `c = 0`, then `V^*` would fix
`W(t)^* e₀` for every `t`; hence the observation of `(V - I) v` vanishes for every `v`,
and injectivity of the observation map (Lemma 10.4) forces `V = I`. The paper excludes
`V_{E₀} = I` using the fixed-space lemma (Lemma 10.5); here `U_{E₀} ≠ I` is a hypothesis.
Continuity of the transport in the energy then gives the interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The first step of Lemma 6.1: if `V_E ≠ I` and `E > 0`, some rebasing of the transport
has `c = (V'^* - I) e₀ ≠ 0`, where `V' = W(t) V W(t)^*` is the rebased endpoint. -/
theorem exists_basepoint_cutC_ne_zero   (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0)  (hE : 0 < E) 
    (hW : IsTransport γ E W) (hV : W (2 * π) ≠ 1) :
    ∃ t ∈ Icc 0 (2 * π),
      cutC (W t * W (2 * π) * ContinuousLinearMap.adjoint (W t)) (basisVec 0) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hV
  set V := W (2 * π)
  ext1 v
  rw [ContinuousLinearMap.one_apply, ← sub_eq_zero]
  refine observation_injective hK hγ' hE hW (V v - v) fun θ hθ => ?_
  have hu := (volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 θ hθ).1
  rw [ContinuousLinearMap.star_eq_adjoint] at hu
  set u := ContinuousLinearMap.adjoint (W θ) (basisVec 0)
  rw [← ContinuousLinearMap.adjoint_inner_left, inner_sub_right]
  change ⟪u, V v⟫_ℂ - ⟪u, v⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, show ContinuousLinearMap.adjoint V u = u by
    have h1 := h θ hθ
    unfold cutC at h1
    rw [sub_eq_zero] at h1
    have h2 := congrArg (ContinuousLinearMap.adjoint (W θ)) h1
    simp [ContinuousLinearMap.mul_def] at h2
    have h3 : ∀ x, ContinuousLinearMap.adjoint (W θ) (W θ x) = x := fun x => by
      rw [← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
    rw [h3] at h2
    exact h2, sub_self]

/-- **Lemma 6.1 (choice of a boundary origin).** Let `γ` be a periodic Lipschitz curve with
`γ' ≠ 0` almost everywhere, `W_E` its transports, `E₀ > 0`, and suppose `U_{E₀} ≠ I`.
Then there are a base point `t ∈ [0, L]` and `ε ∈ (0, E₀]` such that for every
`E ∈ (E₀ - ε, E₀ + ε)` the transport `W'` of the rebased curve `γ(· + t)` has
`c_E = (V_E'^* - I) e₀ ≠ 0`. -/
theorem exists_boundary_origin {γ : ℝ → ℂ}  (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E))
     (hE₀ : 0 < E₀) (hU : monodromy (Ws E₀) ≠ 1) :
    ∃ t ∈ Icc 0 (2 * π), ∃ ε > 0, ε ≤ E₀ ∧ ∀ E ∈ Ioo (E₀ - ε) (E₀ + ε),
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport (fun θ => γ (θ + t)) E W' →
        cutC (W' (2 * π)) (basisVec 0) ≠ 0 := by
  obtain ⟨t, ht, hc⟩ := exists_basepoint_cutC_ne_zero hK hγ' hE₀ (hWs E₀) (by
    intro h1
    apply hU
    rw [monodromy, h1, ← ContinuousLinearMap.star_eq_adjoint, star_one])
  set F : ℝ → Ell2 := fun E =>
    cutC (Ws E t * Ws E (2 * π) * ContinuousLinearMap.adjoint (Ws E t)) (basisVec 0)
  have hadj :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp ((show Tendsto F (𝓝 E₀) (𝓝 (F E₀)) by
    have h1 := tendsto_transport_energy hK hWs E₀ ht
    have h3 :=
      (h1.mul (tendsto_transport_energy hK hWs E₀ ⟨(by positivity), le_rfl⟩)).mul ((hadj.tendsto _).comp h1)
    have h4 : Continuous (fun X : Ell2 →L[ℂ] Ell2 => cutC X (basisVec 0)) := by
      unfold cutC
      exact (hadj.clm_apply continuous_const).sub continuous_const
    exact (h4.tendsto _).comp h3).eventually_ne hc)
  refine ⟨t, ht, min δ E₀, lt_min hδ hE₀, min_le_right _ _, fun E hE W' hW' => ?_⟩
  rw [transport_basepoint hK hper (hWs E) ht hW']
  exact hδF (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hE.1, hE.2, min_le_left δ E₀])

/-- **Lemma 6.1 for a boundary parametrization.** For a boundary parametrization `γ` of `Ω`,
`E₀ > 0` with `U_{E₀} ≠ I`, there are a boundary origin `t` and an interval
`(E₀ - ε, E₀ + ε) ⊂ (0, ∞)` on which every transport of the rebased curve has `c_E ≠ 0`. -/
theorem exists_boundary_origin_of_boundaryParam  
    (hγ : IsBoundaryParam Ω γ) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E))  (hE₀ : 0 < E₀)
    (hU : monodromy (Ws E₀) ≠ 1) :
    ∃ t ∈ Icc 0 (2 * π), ∃ ε > 0, ε ≤ E₀ ∧ ∀ E ∈ Ioo (E₀ - ε) (E₀ + ε),
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport (fun θ => γ (θ + t)) E W' →
        cutC (W' (2 * π)) (basisVec 0) ≠ 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  exact exists_boundary_origin hK hγ.periodic (by
    filter_upwards [hspeed] with θ hθ h0
    rw [h0, norm_zero] at hθ
    exact hc.ne hθ) hWs hE₀ hU

end PolyaNeumann

end
