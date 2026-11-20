module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalRoughChartInjectivity
public import RequestProject.LocalConformalPeriodicBoundaryNull
public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.FiniteFourierChartCompact
public import RequestProject.ReducedFormCentre

/-! The reduced boundary estimate from actual supplied conformal coordinates.
The chart, kernel injection, original spectral residue and compact positive
compression are all constructed by the preceding physical results. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Set Metric Filter Topology ContinuousLinearMap
open scoped InnerProductSpace
local notation "H₀" => nonpositiveFourierSubspace

section SuppliedCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))
include coords

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => coords.halfTrace
local notation "NF" => normalizedConormal
  (localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth)
  (localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth)
  (localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth)

include hγ hτ hcoord in
theorem exists_localConformal_normalized_reduced_boundary_bound
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
    {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ y : L2Z, ℓ y = 0 →
          -(A * ‖projObsDual (Ws E) y‖ ^ 2) ≤
            (⟪y, normalizedPeriodicBoundaryFamily QF Ws E y⟫_ℂ).re := by
  obtain ⟨d, u, v, hinjS, Vchart, hVchart, hchart⟩ :=
    exists_localConformal_fixed_fourier_complement_projectedObservation_injective coords hΓLip hE₀ (hWs E₀) hcut
  let T := finiteFourierChart u v
  let J : ℝ → H₀ →L[ℂ] L2Z := fun E => (NF (E : ℂ)).comp (H₀).subtypeL
  let P : ℝ → L2Z →L[ℂ] L2Z := normalizedPeriodicBoundaryFamily QF Ws
  let Preg : ℝ → L2Z →L[ℂ] L2Z := normalizedPeriodicRegularFamily QF E₀ Ws
  let S := fun E => projObsDual (Ws E)
  obtain ⟨w, hw⟩ := normalizedNeumannResidue_factorization QF coords.bounded coords.lipschitz hE₀.le
  obtain ⟨Vcomp, hVcomp, hcomp, _⟩ := h1ComplementForm_isUnit_near coords.bounded coords.lipschitz hE₀.le
  have hcutNear := eventually_cutC_ne hΓLip hWs E₀ hcut
  let Vbase : Set ℝ := Vchart ∩ Vcomp ∩
    {E | cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0}
  have hVbase := inter_mem (inter_mem hVchart hVcomp) hcutNear
  let U : Set ℝ := {E | E ∈ Vbase ∧ 0 < E ∧
    ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E}
  have hbase (E : ℝ) (hEU : E ∈ U) :=
    summable_correctedRemainderMatrix hΓLip (hWs E) hEU.1.2
  have hsa : ∀ E ∈ U, IsSelfAdjoint (P E) := by
    intro E hEU
    exact normalizedPeriodicBoundaryFamily_isSelfAdjoint QF Ws hΓLip (hWs E) (hbase E hEU)
  have hnullP : ∀ E ∈ U, P E ∘L J E = 0 := by
    intro E hEU
    exact localConformalPeriodicBoundaryNull_comp_subtype coords hγ hτ hcoord Ws hEU.2.1.le hEU.2.2 hΓLip (hWs E) hEU.1.2
  have hnullS : ∀ E ∈ U, S E ∘L J E = 0 := by
    intro E hEU
    apply ContinuousLinearMap.ext
    intro b
    exact localConformalVekuaForward_projObsDual_eq_zero coords E hEU.2.1.le hΓLip (hWs E) (b : L2Z) b.property
  have hpole : ∀ E ∈ U, P E = ((-2 / (E - E₀) : ℝ) : ℂ) •
      ∑ j, InnerProductSpace.rankOne ℂ (w j) (w j) + Preg E := by
    intro E hEU
    change normalizedPeriodicBoundaryFamily QF Ws E = _
    rw [normalizedPeriodicBoundaryFamily_eq_pole_add_regular QF coords.bounded coords.lipschitz Ws hE₀.le
      (h1HelmholtzForm_isUnit coords.bounded coords.lipschitz hEU.2.1.le hEU.2.2) (hcomp E hEU.1.1.2),
      hw]
  have hu₀ := h1ComplementForm_isUnit coords.bounded coords.lipschitz hE₀.le
  have hPreg : ContinuousAt Preg E₀ :=
    continuousAt_normalizedPeriodicRegularFamily QF hu₀ hΓLip hWs hcut
  have hS := tendsto_projObsDual_energy hΓLip hWs E₀ hcut
  have hbase₀ := summable_correctedRemainderMatrix hΓLip (hWs E₀) hcut
  obtain ⟨D, hD, hreg⟩ := localConformal_finiteFourierChart_regular_compression
    coords hE₀.le hu₀ (Ws E₀) hbase₀ u v
  have hreg' : adjoint T ∘L Preg E₀ ∘L T =
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + D := by
    change adjoint T ∘L normalizedPeriodicRegularFamily QF E₀ Ws E₀ ∘L T = _
    rw [normalizedPeriodicRegularFamily_eq QF E₀ E₀ Ws hbase₀]
    assumption
  have hinj' : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint T (w j), z⟫_ℂ = 0) →
      S E₀ (T z) = 0 → z = 0 := by
    intro z _ hz
    apply hinjS
    change projObsDual (Ws E₀) (T z) = projObsDual (Ws E₀) (T 0)
    rw [map_zero, map_zero]
    assumption
  obtain ⟨A, hA, V, hV, hbound⟩ := chart_reduced_boundary_bound_on_energy_set H₀ J T E₀ U
    (fun E hEU => hchart E hEU.1.1.1) P Preg S w hsa hnullP hnullS hpole
    hPreg hS 4 (by norm_num) D hD hreg' hinj'
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hVbase)
  refine ⟨A, δ, hA, hδ, ?_⟩
  intro E hE hnear hnr
  have hball : E ∈ ball E₀ δ := mem_ball.mpr (id hnear)
  obtain ⟨hEV, hEbase⟩ := hδsub hball
  exact hbound E hEV ⟨hEbase, hE, hnr⟩

end SuppliedCoordinates
end PolyaNeumann
end
