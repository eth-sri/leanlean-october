module

public import RequestProject.LocalConformalFixedComplement
public import RequestProject.LocalConformalRadialVekua
public import RequestProject.ObservationLp
public import RequestProject.ReducedForm

/-!
# Genuine half-regular reduced kernels in supplied conformal coordinates

A half-regular normalized load is the half-smoothed unitary Fourier
transform of a genuine boundary L2 element. The projected observation
kernel can therefore be treated by the actual driven construction after
subtracting the genuine radial wave. The resulting load belongs to the
actual normalized conormal range. An invertible fixed chart then forces
its complement component to vanish.

The half-order condition is stated explicitly. This file does not infer
Sobolev smoothing from finite rank, and does not claim the missing
bootstrap for arbitrary normalized L2 loads. The constructions in this module
are part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

/-- The genuine ordinary boundary L2 load represented by a half-regular
normalized Fourier vector. -/
def halfRegularCoordinateLoad (y : L2Z)
    (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ)) : BoundaryL2 :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy)

variable {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- The unitary Fourier normalization is exact, including frequency zero. -/
theorem halfRegularCoordinateLoad_normalized (y : L2Z)
    (hy : IsSobolevSeq (1 / 2) y) :
    sobolevSmoothing (1 / 2) (by norm_num)
      (boundaryFourier (halfRegularCoordinateLoad y hy)) = y := by
  rw [halfRegularCoordinateLoad, boundaryFourier.apply_symm_apply]
  apply lp.ext
  funext n
  change fromL2 (1 / 2) (sobVec (1 / 2) y hy) n = y n
  rw [fromL2_sobVec]

/-- The normalized projected observation agrees with the actual ordinary
L2 observation. The factor sqrt(2 pi) is retained explicitly. -/
theorem projObsDual_halfRegularCoordinateLoad
    (hγLip : LipschitzWith L γ)
    (hW : IsTransport γ E W) (y : L2Z)
    (hy : IsSobolevSeq (1 / 2) y) :
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W y =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (halfRegularCoordinateLoad y hy)) := by
  have h := projObsDual_boundary_normalized hγLip hW (halfRegularCoordinateLoad y hy)
  rwa [halfRegularCoordinateLoad_normalized, map_smul] at h

private theorem reduced_observationAdj_sub_smul
    (hγLip : LipschitzWith L γ)
    (hW : IsTransport γ E W) (g r : BoundaryL2) (t : ℂ) :
    observationAdj W ((g - t • r : BoundaryL2) : ℝ → ℂ) =
      observationAdj W (g : ℝ → ℂ) - t • observationAdj W (r : ℝ → ℂ) := by
  have hg := integrable_boundary_observation_load hγLip hW g
  have hr := integrable_boundary_observation_load hγLip hW r
  rw [observationAdj, observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    _ = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0) -
          t • (r θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub g (t • r), Lp.coeFn_smul t r] with θ hs ht
      simp_all [Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul, smul_eq_mul]
    _ = _ := by
      have hsplit := integral_sub hg (hr.smul t)
      simp_all [Pi.smul_apply, integral_smul]

private theorem reduced_eq_smul_of_cutProj_eq_zero
    (c x : Ell2) (h : cutProj c x = 0) :
    x = (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, x⟫_ℂ) • c := by
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at h
  grind

private theorem reduced_injective_of_isUnit
    (B : L2Z →L[ℂ] L2Z) (hB : IsUnit B) : Function.Injective B := by
  obtain ⟨u, rfl⟩ := hB
  intro x y hxy
  have h := congrArg (fun z : L2Z => (↑u⁻¹ : L2Z →L[ℂ] L2Z) z) hxy
  simpa only [← ContinuousLinearMap.mul_apply, Units.inv_mul,
    ContinuousLinearMap.one_apply] using h

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' Metric.ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' Metric.ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hinj : InjOn F (Metric.ball (0 : ℂ) 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "H₀" => nonpositiveFourierSubspace
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (WithTop.coe_le_coe.mpr le_top))

variable {L : NNReal}

include hb hL hhol hinj hC hK e he hsource hes in
/-- For a genuine ordinary coordinate L2 load, zero projected observation
places its normalized load in the actual full nonpositive conormal range.
The radial subtraction is the actual zero-mode H1 Vekua wave. -/
theorem localConformal_projectedObservation_L2_kernel_mem_conormal_range
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (g : BoundaryL2)
    (hproj : cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
      (observationAdj W g) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧
      NF E b = sobolevSmoothing (1 / 2) (by norm_num)
        (boundaryFourier g) := by
  let c  := cutC (W (2 * Real.pi)) (basisVec 0)
  let α  := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W g⟫_ℂ)
  let t  := -Complex.I * α
  let r  := localConformalRadialCoordinateLoad F hΓLip E 1
  have hrad : observationAdj W r = Complex.I • c := by
    simpa only [mul_one] using
      localConformalRadialCoordinateLoad_observationAdj F hΓLip hW 1
  have hti : t * Complex.I = α := by
    calc
      (-Complex.I * α) * Complex.I = -(Complex.I * Complex.I) * α := by ring
      _ = α := by norm_num
  let g₀  := g - t • r
  have hO : observationAdj W g₀ = 0 := by
    rw [reduced_observationAdj_sub_smul hΓLip hW, reduced_eq_smul_of_cutProj_eq_zero c _ hproj, hrad,
      smul_smul, hti, sub_self]
  let b₀  := physicalDrivenKernelInput hΓLip hΓF hW
    g₀ (Lp.memLp g₀) hO
  have hb₀ : IsNonpositiveFourierSupport b₀ :=
    physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource
      hΓLip hE hW g₀ (Lp.memLp g₀) hO
  have hNC₀ : NF E b₀ = sobolevSmoothing (1 / 2) (by norm_num)
      (boundaryFourier g₀) := by
    simpa only [physicalDrivenKernelCoordinateLoad, Lp.toLp_coeFn] using physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW
        g₀ (Lp.memLp g₀) hO
  have hNCr : NF E radialVekuaInput =
      sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier r) := by
    simpa only [one_smul] using
      localConformalRadial_normalizedConormal_eq_coordinateLoad hR F hFs hb hL hhol hinj
        hC hK e he hsource hes hΓLip hE 1
  refine ⟨b₀ + t • radialVekuaInput, ?_, ?_⟩
  · intro n hn
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      hb₀ n hn, radialVekuaInput_nonpositive n hn, smul_zero, add_zero]
  · rw [map_add, map_smul, hNC₀, hNCr]
    rw [map_sub, map_smul, map_sub, map_smul]
    abel

include hb hL hhol hinj hC hK e he hsource hes in
/-- Half-regular normalized inputs with zero projected observation lie in
the actual conormal range. Regularity is used only to construct their true
ordinary L2 load, not as a substitute for the range identity. -/
theorem localConformal_projectedObservation_half_regular_kernel_mem_conormal_range
    (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : IsSobolevSeq (1 / 2) y)
    (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF E b = y := by
  have hproj := projObsDual_halfRegularCoordinateLoad hΓLip hW y hy
  rw [hobs, smul_zero] at hproj
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_L2_kernel_mem_conormal_range hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW
        (halfRegularCoordinateLoad y hy) hproj.symm
  exact ⟨b, hbn, hb'.trans (halfRegularCoordinateLoad_normalized y hy)⟩

include hb hL hhol hinj hC hK e he hsource hes in
/-- The true projected observation is injective on half-regular vectors
of an actual fixed complement chart. The chart hypothesis is an actual
unit, rather than the desired reduced injectivity conclusion. -/
theorem localConformal_fixed_complement_half_regular_kernel_eq_zero
    (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (T : H₀ᗮ →L[ℂ] L2Z)
    (hunit : IsUnit ((NF E).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      T ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hz : IsSobolevSeq (1 / 2) (T z))
    (hobs : projObsDual W (T z) = 0) : z = 0 := by
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_half_regular_kernel_mem_conormal_range hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW (T z) hz hobs
  let a : H₀ := ⟨b, hbn⟩
  exact (chart_range_inter_eq_zero H₀ ((NF E).comp (H₀).subtypeL) T
    (reduced_injective_of_isUnit _ hunit) a z hb'.symm).1

end PhysicalCoordinates

end PolyaNeumann

end
