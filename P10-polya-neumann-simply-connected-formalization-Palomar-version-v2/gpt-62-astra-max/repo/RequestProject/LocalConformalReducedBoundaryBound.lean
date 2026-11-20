module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalRoughChartInjectivity
public import RequestProject.LocalConformalPeriodicBoundaryNull
public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.FiniteFourierChartCompact
public import RequestProject.ReducedFormCentre
public import RequestProject.PlanarNotation

/-! The reduced boundary estimate from actual supplied conformal coordinates.
The chart, kernel injection, original spectral residue and compact positive
compression are all constructed by the preceding physical results. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace PolyaNeumann
open Set Metric Filter Topology ContinuousLinearMap
open scoped InnerProductSpace
local notation "H₀" => nonpositiveFourierSubspace

private theorem reduced_cutC_continuousAt_energy
    {γ : ℝ → ℂ} {L : NNReal} {Ws : ℝ → TransportPath}
    (hΓLip : LipschitzWith L γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) :
    ContinuousAt (fun E => cutVector (Ws E)) E₀ := by
  have ht := tendsto_transport_energy hΓLip hWs E₀
    (show anglePeriod ∈ angleInterval from ⟨Real.two_pi_pos.le, le_rfl⟩)
  
  exact (((continuous_eval_const (basisVec 0)).tendsto _).comp
    (((ContinuousLinearMap.adjoint  (E := Ell2) (F := Ell2)).continuous.tendsto _).comp ht)).sub tendsto_const_nhds

section SuppliedCoordinates

theorem exists_localConformal_normalized_reduced_boundary_bound (Φ : DiskCoordinates) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) (Ws : ℝ → TransportPath)
    (hWs : ∀ E, IsTransport Φ.boundary E (Ws E)) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutVector (Ws E₀) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity Φ.domain E₀) → ℂ),
        ∀ y : L2Z, ℓ y = 0 →
          -(A * ‖projObsDual (Ws E) y‖ ^ 2) ≤
            (⟪y, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E y⟫_ℂ).re := by
  obtain ⟨d, u, v, _, hv, hinjS, Vchart, hVchart, hchart, _⟩ :=
    exists_localConformal_fixed_fourier_complement_projectedObservation_injective
      Φ hΓLip hE₀ (hWs E₀) hcut
  let T  := finiteFourierChart u v
  let J : ℝ → H₀ →L[ℂ] L2Z := fun E => ((normalizedConormal
  (localConformalVelocityCircle_isWL1_half Φ)
  (localConformalHardyPrimitiveMultiplier_isWL1 Φ)
  (localConformalCenteredCircle_isWL1_half Φ)) (E : ℂ)).comp (H₀).subtypeL
  let P  := normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws
  let Preg  := normalizedPeriodicRegularFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ Ws
  let S  := fun E => projObsDual (Ws E)
  let w := normalizedNeumannResonanceMode (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain hE₀.le
  obtain ⟨Vcomp, hVcomp, hcomp, _⟩ := h1ComplementForm_isUnit_near Φ.bounded Φ.lipschitzDomain hE₀.le
  have hcutNear := (reduced_cutC_continuousAt_energy hΓLip hWs E₀).eventually_ne hcut
  let Vbase  := Vchart ∩ Vcomp ∩
    {E | cutVector (Ws E) ≠ 0}
  have hVbase  := inter_mem (inter_mem hVchart hVcomp) hcutNear
  let U : Set ℝ := {E | E ∈ Vbase ∧ 0 < E ∧
    ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E}
  have hbase (E : ℝ) (hEU : E ∈ U)  :=
    herglotz_transfer_kernel_summable Φ hΓLip (hWs E) hEU.1.2
  have hsa : ∀ E ∈ U, IsSelfAdjoint (P E) := by
    intro E hEU
    exact normalizedPeriodicBoundaryFamily_isSelfAdjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws hΓLip (hWs E) (hbase E hEU)
  have hnullP : ∀ E ∈ U, P E ∘L J E = 0 := by
    intro E hEU
    exact localConformalPeriodicBoundaryNull_comp_subtype Φ hγ hτ hcoord Ws hEU.2.1.le hEU.2.2 hΓLip (hWs E) hEU.1.2
  have hnullS : ∀ E ∈ U, S E ∘L J E = 0 := by
    intro E hEU
    apply ContinuousLinearMap.ext
    intro b
    exact localConformalVekuaForward_projObsDual_eq_zero Φ E hEU.2.1.le hΓLip (hWs E) (b : L2Z) b.property
  have hpole : ∀ E ∈ U, P E = ((-2 / (E - E₀) : ℝ) : ℂ) •
      ∑ j, InnerProductSpace.rankOne ℂ (w j) (w j) + Preg E := by
    intro E hEU
    change normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E = _
    rw [normalizedPeriodicBoundaryFamily_eq_pole_add_regular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain Ws hE₀.le
      (h1HelmholtzForm_isUnit Φ.bounded Φ.lipschitzDomain hEU.2.1.le hEU.2.2) (hcomp E hEU.1.1.2),
      normalizedNeumannResidue_eq_original_basis (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain hE₀.le]
  have hΓ4 := Φ.boundaryC4
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) Φ.boundary := hΓ4.of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 anglePeriod) isCompact_Icc
  have hΓ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval,
      ‖deriv Φ.boundary x - deriv Φ.boundary y‖ ≤ B * |x - y| := by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h
  have hu₀ := h1ComplementForm_isUnit Φ.bounded Φ.lipschitzDomain hE₀.le
  have hPreg  :=
    continuousAt_normalizedPeriodicRegularFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) hu₀ hΓLip hΓ' hWs hcut
  have hS  := tendsto_projObsDual_energy hΓLip hWs E₀ hcut
  have hbase₀ := herglotz_transfer_kernel_summable Φ hΓLip (hWs E₀) hcut
  obtain ⟨D, hD, hreg⟩ := localConformal_finiteFourierChart_regular_compression
    Φ Φ.chart Φ.chart_eq Φ.source Φ.smoothInverse hE₀.le hu₀ (Ws E₀) hbase₀ u v
  have hreg' : adjoint T ∘L Preg E₀ ∘L T =
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + D := by
    change adjoint T ∘L normalizedPeriodicRegularFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ Ws E₀ ∘L T = _
    rw [normalizedPeriodicRegularFamily_eq (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E₀ Ws hbase₀]
    exact hreg
  have hinj' : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint T (w j), z⟫_ℂ = 0) →
      S E₀ (T z) = 0 → z = 0 := by
    intro z _ hz
    apply hinjS
    change projObsDual (Ws E₀) (T z) = projObsDual (Ws E₀) (T 0)
    rw [map_zero, map_zero]
    exact hz
  obtain ⟨A, hA, V, hV, hbound⟩ := chart_reduced_boundary_bound_on_energy_set H₀ J T E₀ U
    (fun E hEU => hchart E hEU.1.1.1) P Preg S w hsa hnullP hnullS hpole
    hPreg hS 4 (by norm_num) D hD hreg' hinj'
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hVbase)
  refine ⟨A, δ, hA, hδ, ?_⟩
  intro E hE hnear hnr
  have hball : E ∈ ball E₀ δ := mem_ball.mpr (hnear)
  obtain ⟨hEV, hEbase⟩ := hδsub hball
  exact hbound E hEV ⟨hEbase, hE, hnr⟩

end SuppliedCoordinates
end PolyaNeumann
end
