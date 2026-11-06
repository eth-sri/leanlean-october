module

public import RequestProject.LocalConformalRoughChartInjectivity
public import RequestProject.LocalConformalPeriodicBoundaryNull
public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.FiniteFourierChartCompact
public import RequestProject.ReducedFormCentre

/-! The reduced boundary estimate from actual supplied conformal coordinates.
The chart, kernel injection, original spectral residue and compact positive
compression are all constructed by the preceding physical results. -/

@[expose] public section
noncomputable section
namespace PolyaNeumann
open Set Metric Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ContDiff
local notation "H₀" => nonpositiveFourierSubspace

section SuppliedCoordinates

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
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem exists_localConformal_normalized_reduced_boundary_bound
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    Ws (hWs : ∀ E, IsTransport ΓF E (Ws E))
     (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ y : L2Z, ℓ y = 0 →
          -(A * ‖projObsDual (Ws E) y‖ ^ 2) ≤
            (⟪y, normalizedPeriodicBoundaryFamily QF Ws E y⟫_ℂ).re := by
  obtain ⟨d, u, v, _, hv, hinjS, Vchart, hVchart, hchart, _⟩ :=
    exists_localConformal_fixed_fourier_complement_projectedObservation_injective
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE₀ (hWs E₀) hcut
  let T : H₀ᗮ →L[ℂ] L2Z := finiteFourierChart u v
  obtain ⟨Vcomp, hVcomp, hcomp, _⟩ := h1ComplementForm_isUnit_near hb hL hE₀.le
  have hVbase := inter_mem (inter_mem hVchart hVcomp) ((show ContinuousAt (fun E => cutC (Ws E (2 * Real.pi)) (basisVec 0)) E₀ by
    exact (((continuous_eval_const (basisVec 0)).tendsto _).comp (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.tendsto _).comp (tendsto_transport_energy hΓLip hWs E₀ (⟨Real.two_pi_pos.le, le_rfl⟩)))).sub tendsto_const_nhds).eventually_ne hcut)
  let U := {E | E ∈ Vchart ∩ Vcomp ∩ {E | cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0} ∧ 0 < E ∧
    ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E}
  have hbase E (hEU : E ∈ U) :
      Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2 :=
    localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip (hWs E) hEU.1.2
  obtain ⟨B, hB⟩ := ((contDiff_physicalCircleTrace_four_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).of_le (by norm_num)).deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  have hu₀ := h1ComplementForm_isUnit hb hL hE₀.le
  have hbase₀ := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip (hWs E₀) hcut
  obtain ⟨D, hD, hreg⟩ := localConformal_finiteFourierChart_regular_compression
    hR F hFs hb hL hhol hinj hC e he hsource hes hE₀.le hu₀ (Ws E₀) hbase₀ u v
  obtain ⟨A, hA, V, hV, hbound⟩ := chart_reduced_boundary_bound_on_energy_set H₀ (fun E => ((normalizedConormal (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs)) E).comp (H₀).subtypeL) T E₀ U
    (fun E hEU => hchart E hEU.1.1.1) (normalizedPeriodicBoundaryFamily QF Ws) (normalizedPeriodicRegularFamily QF E₀ Ws) (fun E => projObsDual (Ws E)) (normalizedNeumannResonanceMode QF hb hL hE₀.le) (by
      intro E hEU
      exact normalizedPeriodicBoundaryFamily_isSelfAdjoint QF Ws hΓLip (hWs E) (hbase E hEU)) (by
      intro E hEU
      exact localConformalPeriodicBoundaryNull_comp_subtype hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ hτ hcoord Ws hEU.2.1.le hEU.2.2 hΓLip (hWs E) hEU.1.2) (by
      intro E hEU
      apply ContinuousLinearMap.ext
      intro b
      exact localConformalVekuaForward_projObsDual_eq_zero hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E hEU.2.1.le hΓLip (hWs E) b b.property) (by
      intro E hEU
      change normalizedPeriodicBoundaryFamily QF Ws E = _
      rw [normalizedPeriodicBoundaryFamily_eq_pole_add_regular QF hb hL Ws hE₀.le
        (h1HelmholtzForm_isUnit hb hL hEU.2.1.le hEU.2.2) (hcomp E hEU.1.1.2),
        normalizedNeumannResidue_eq_original_basis QF hb hL hE₀.le])
    (continuousAt_normalizedPeriodicRegularFamily QF hu₀ hΓLip (by
      intro x hx y hy
      have h := hB.dist_le_mul x hx y hy
      rwa [dist_eq_norm, Real.dist_eq] at h) hWs hcut) (tendsto_projObsDual_energy hΓLip hWs E₀ hcut) 4 (by norm_num) D hD (by
      change adjoint T ∘L normalizedPeriodicRegularFamily QF E₀ Ws E₀ ∘L T = _
      rw [normalizedPeriodicRegularFamily_eq QF E₀ E₀ Ws hbase₀]
      exact hreg) (by
      intro z _ hz
      apply hinjS
      change projObsDual (Ws E₀) (T z) = projObsDual (Ws E₀) (T 0)
      rw [map_zero, map_zero]
      exact hz)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hVbase)
  refine ⟨A, δ, hA, hδ, ?_⟩
  intro E hE hnear hnr
  obtain ⟨hEV, hEbase⟩ := hδsub (mem_ball.mpr (by simpa [Real.dist_eq] using hnear))
  exact hbound E hEV ⟨hEbase, hE, hnr⟩

end SuppliedCoordinates
end PolyaNeumann
end
