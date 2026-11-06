module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalRoughChartInjectivity
public import RequestProject.LocalConformalPeriodicBoundaryNull
public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.FiniteFourierChartCompact
public import RequestProject.ReducedFormCentre

/-! The reduced boundary estimate from actual supplied conformal coordinates.
The chart, kernel injection, original spectral residue and compact positive
compression are all constructed by the preceding physical results. -/

@[expose] public section

open scoped ContDiff

namespace PolyaNeumann
open Set Metric Filter Topology ContinuousLinearMap
open scoped InnerProductSpace
local notation "H₀" => nonpositiveFourierSubspace

private theorem reduced_cutC_continuousAt_energy
      {Ws : ℝ → ℝ → ComplexEnd Ell2}
    (hΓLip : LipschitzWith L γ) (hWs : ∀ E, IsTransport γ E (Ws E)) E₀ :
    ContinuousAt (fun E => cutC (Ws E circlePeriod) (basisVec 0)) E₀ := by
  have ht := tendsto_transport_energy hΓLip hWs E₀
    ((⟨Real.two_pi_pos.le, le_rfl⟩))
  have ha := ((continuous_eval_const (basisVec 0)).tendsto _).comp
    (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.tendsto _).comp ht)
  exact ha.sub tendsto_const_nhds

section SuppliedCoordinates

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
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "NF" => normalizedConormal
  (localConformalVelocityCircle_isWL1_half hR F hFs)
  (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)
  (localConformalCenteredCircle_isWL1_half hR F hFs)

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem exists_localConformal_normalized_reduced_boundary_bound
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → ComplexEnd Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
    {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ circlePeriod) (basisVec 0) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ y : L2Z, ℓ y = 0 →
          -(A * ‖projObsDual (Ws E) y‖ ^ 2) ≤
            (⟪y, normalizedPeriodicBoundaryFamily QF Ws E y⟫_ℂ).re := by
  obtain ⟨d, u, v, _, hv, hinjS, Vchart, hVchart, hchart, _⟩ :=
    exists_localConformal_fixed_fourier_complement_projectedObservation_injective
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE₀ (hWs E₀) hcut
  let T  := finiteFourierChart u v
  let J : ℝ → H₀ →L[ℂ] L2Z := fun E => (NF E).comp (H₀).subtypeL
  let P  := normalizedPeriodicBoundaryFamily QF Ws
  let Preg  := normalizedPeriodicRegularFamily QF E₀ Ws
  let S  := fun E => projObsDual (Ws E)
  let w := normalizedNeumannResonanceMode QF hb hL hE₀.le
  obtain ⟨Vcomp, hVcomp, hcomp, _⟩ := h1ComplementForm_isUnit_near hb hL hE₀.le
  have hcutNear := (reduced_cutC_continuousAt_energy hΓLip hWs E₀).eventually_ne hcut
  let Vbase  := Vchart ∩ Vcomp ∩
    {E | cutC (Ws E circlePeriod) (basisVec 0) ≠ 0}
  have hVbase  := inter_mem (inter_mem hVchart hVcomp) hcutNear
  let U  := {E | E ∈ Vbase ∧ 0 < E ∧
    ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E}
  have hbase (E : ℝ) (hEU : E ∈ U)  :=
    localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip (hWs E) hEU.1.2
  have hsa : ∀ E ∈ U, IsSelfAdjoint (P E) := by
    intro E hEU
    exact normalizedPeriodicBoundaryFamily_isSelfAdjoint QF Ws hΓLip (hWs E) (hbase E hEU)
  have hnullP : ∀ E ∈ U, P E ∘L J E = 0 := by
    intro E hEU
    exact localConformalPeriodicBoundaryNull_comp_subtype hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord Ws hEU.2.1.le hEU.2.2 hΓLip (hWs E) hEU.1.2
  have hnullS : ∀ E ∈ U, S E ∘L J E = 0 := by
    intro E hEU
    apply ContinuousLinearMap.ext
    intro b
    exact localConformalVekuaForward_projObsDual_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hEU.2.1.le hΓLip (hWs E) b b.property
  have hpole : ∀ E ∈ U, P E = ((-2 / (E - E₀) : ℝ) : ℂ) •
      ∑ j, InnerProductSpace.rankOne ℂ (w j) (w j) + Preg E := by
    intro E hEU
    change normalizedPeriodicBoundaryFamily QF Ws E = _
    rw [normalizedPeriodicBoundaryFamily_eq_pole_add_regular QF hb hL Ws hE₀.le
      (h1HelmholtzForm_isUnit hb hL hEU.2.1.le hEU.2.2) (hcomp E hEU.1.1.2),
      normalizedNeumannResidue_eq_original_basis QF hb hL hE₀.le]
  have hΓ4 := contDiff_physicalCircleTrace_four_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) ΓF := hΓ4.of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc 0 circlePeriod) isCompact_Icc
  have hΓ' : ∀ x ∈ boundaryInterval, ∀ y ∈ boundaryInterval,
      ‖deriv ΓF x - deriv ΓF y‖ ≤ B * |x - y| := by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h
  have hu₀ := h1ComplementForm_isUnit hb hL hE₀.le
  have hPreg  :=
    continuousAt_normalizedPeriodicRegularFamily QF hu₀ hΓLip hΓ' hWs hcut
  have hS  := tendsto_projObsDual_energy hΓLip hWs E₀ hcut
  have hbase₀ := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip (hWs E₀) hcut
  obtain ⟨D, hD, hreg⟩ := localConformal_finiteFourierChart_regular_compression
    hR F hFs hb hL hhol hinj hC e he hsource hes hE₀.le hu₀ (Ws E₀) hbase₀ u v
  have hreg' : adjoint T ∘L Preg E₀ ∘L T =
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + D := by
    change adjoint T ∘L normalizedPeriodicRegularFamily QF E₀ Ws E₀ ∘L T = _
    rw [normalizedPeriodicRegularFamily_eq QF E₀ E₀ Ws hbase₀]
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
  have hball : E ∈ ball E₀ δ := mem_ball.mpr (by simpa only [Real.dist_eq] using hnear)
  obtain ⟨hEV, hEbase⟩ := hδsub hball
  exact hbound E hEV ⟨hEbase, hE, hnr⟩

end SuppliedCoordinates
end PolyaNeumann