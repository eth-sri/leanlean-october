module

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
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


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff

/-- The genuine ordinary boundary L2 load represented by a half-regular
normalized Fourier vector. -/
def halfRegularCoordinateLoad (y : L2Z)
    (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ)) : BoundaryL2 :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy)

/-- The unitary Fourier normalization is exact, including frequency zero. -/
theorem halfRegularCoordinateLoad_normalized y
    hy :
    sobolevSmoothing (1 / 2) (by norm_num)
      (boundaryFourier (halfRegularCoordinateLoad y hy)) = y := by
  rw [halfRegularCoordinateLoad, boundaryFourier.apply_symm_apply]
  apply lp.ext
  funext n
  change fromL2 (1 / 2) (sobVec (1 / 2) y hy) n = _
  rw [fromL2_sobVec]

private theorem reduced_observationAdj_sub_smul
      
     (hγLip : LipschitzWith L γ)
    (hW : IsTransport γ E W) (g r : BoundaryL2) (t : ℂ) :
    observationAdj W ((g - t • r : BoundaryL2) : ℝ → ℂ) =
      observationAdj W (g : ℝ → ℂ) - t • observationAdj W (r : ℝ → ℂ) := by
  rw [observationAdj, observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    _ = ∫ θ in Ioc 0 (2 * Real.pi),
        g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0) -
          t • (r θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub g (t • r), Lp.coeFn_smul t r] with θ hs ht
      simp only [hs, ht, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul,
        smul_eq_mul]
    _ = _ := by
      have hsplit := integral_sub (integrable_boundary_observation_load hγLip hW g) ((integrable_boundary_observation_load hγLip hW r).smul t)
      simp only [Pi.smul_apply] at hsplit
      rw [integral_smul] at hsplit
      simpa only [smul_smul] using hsplit

private theorem reduced_eq_smul_of_cutProj_eq_zero
    (c x : Ell2) (h : cutProj c x = 0) :
    x = (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, x⟫_ℂ) • c := by
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at h
  exact sub_eq_zero.mp h

private theorem reduced_injective_of_isUnit
    (B : L2Z →L[ℂ] L2Z) (hB : IsUnit B) : Function.Injective B := by
  obtain ⟨u, rfl⟩ := hB
  intro x y hxy
  simpa [← ContinuousLinearMap.mul_apply] using congrArg (fun z => (↑u⁻¹ : L2Z →L[ℂ] L2Z) z) hxy

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Metric.ball 0 R))
    (hb : Bornology.IsBounded (F '' Metric.ball 0 1))
    (hL : IsLipschitzDomain (F '' Metric.ball 0 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hinj : InjOn F (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : Metric.closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

local notation "H₀" => nonpositiveFourierSubspace
local notation "NF" => normalizedConormal (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs)
local notation "ΓF" => physicalCircleTrace F

include hb hL hhol hinj hC hK e he hsource hes in
/-- For a genuine ordinary coordinate L2 load, zero projected observation
places its normalized load in the actual full nonpositive conormal range.
The radial subtraction is the actual zero-mode H1 Vekua wave. -/
theorem localConformal_projectedObservation_L2_kernel_mem_conormal_range
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    (g : BoundaryL2)
    (hproj : cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
      (observationAdj W (g : ℝ → ℂ)) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧
      NF (E : ℂ) b = sobolevSmoothing (1 / 2) (by norm_num)
        (boundaryFourier g) := by
  let c := cutC (W (2 * Real.pi)) (basisVec 0)
  let α := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W g⟫_ℂ)
  let t := -Complex.I * α
  let r := localConformalRadialCoordinateLoad F hΓLip E 1
  let g₀ := g - t • r
  have hO : observationAdj W g₀ = 0 := by
    dsimp only [g₀]
    rw [reduced_observationAdj_sub_smul hΓLip hW, reduced_eq_smul_of_cutProj_eq_zero c _ hproj, show observationAdj W r = Complex.I • c by
      simpa [r, c] using
        localConformalRadialCoordinateLoad_observationAdj F hΓLip hW 1,
      smul_smul, show t * Complex.I = α by
        dsimp only [t]
        calc
          _ = -(Complex.I * Complex.I) * α := by ring
          _ = α := by rw [Complex.I_mul_I]; ring, sub_self]
  let b₀ := physicalDrivenKernelInput hΓLip (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) hW
    g₀ (Lp.memLp g₀) hO
  have hb₀ : IsNonpositiveFourierSupport b₀ :=
    physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource
      hΓLip hE hW g₀ (Lp.memLp g₀) hO
  refine ⟨b₀ + t • radialVekuaInput, ?_, ?_⟩
  · intro n hn
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      hb₀ n hn, radialVekuaInput_nonpositive n hn, smul_zero, add_zero]
  · rw [map_add, map_smul, show NF E b₀ = sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g₀) by
      have h := physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad hR F hFs hb hL
        hhol hinj hC hK e he hsource hes hΓLip hE hW
          g₀ (Lp.memLp g₀) hO
      simpa [b₀, physicalDrivenKernelCoordinateLoad] using h, show NF E radialVekuaInput = sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier r) by
      simpa [r] using
        localConformalRadial_normalizedConormal_eq_coordinateLoad hR F hFs hb hL hhol hinj
          hC hK e he hsource hes hΓLip hE 1]
    dsimp only [g₀]
    rw [map_sub, map_smul, map_sub, map_smul]
    abel

include hb hL hhol hinj hC hK e he hsource hes in
/-- Half-regular normalized inputs with zero projected observation lie in
the actual conormal range. Regularity is used only to construct their true
ordinary L2 load, not as a substitute for the range identity. -/
theorem localConformal_projectedObservation_half_regular_kernel_mem_conormal_range
     (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : IsSobolevSeq (1 / 2) y)
    (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF (E : ℂ) b = y := by
  have hproj : Real.sqrt (2 * Real.pi) • projObsDual W y = cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) (observationAdj W (halfRegularCoordinateLoad y hy)) := by
    have h := projObsDual_boundary_normalized hΓLip hW (halfRegularCoordinateLoad y hy)
    rw [halfRegularCoordinateLoad_normalized, map_smul] at h
    exact h
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
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    (T : H₀ᗮ →L[ℂ] L2Z)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      T ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hz : IsSobolevSeq (1 / 2) (T z : ℤ → ℂ))
    (hobs : projObsDual W (T z) = 0) : z = 0 := by
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_half_regular_kernel_mem_conormal_range hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW (T z) hz hobs
  exact (chart_range_inter_eq_zero H₀ ((NF E).comp (H₀).subtypeL) T
    (reduced_injective_of_isUnit _ hunit) ⟨b, hbn⟩ z hb'.symm).1

end PhysicalCoordinates

end PolyaNeumann

end
