module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter
open scoped InnerProductSpace

/-- The genuine ordinary boundary L2 load represented by a half-regular
normalized Fourier vector. -/
def halfRegularCoordinateLoad (y : L2Z)
    hy  :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (y : FourierSeq) hy)

/-- The unitary Fourier normalization is exact, including frequency zero. -/
theorem halfRegularCoordinateLoad_normalized y
    hy :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (halfRegularCoordinateLoad y hy)) = y := by
  rw [halfRegularCoordinateLoad, boundaryFourier.apply_symm_apply]
  apply lp.ext
  funext n
  change fromL2 (1 / 2) (sobVec (1 / 2) y hy) n = y n
  rw [fromL2_sobVec]

section
variable {γ } {L } {E } {W } (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
include γ L E W hγLip hW

/-- The normalized projected observation agrees with the actual ordinary
L2 observation. The factor sqrt(2 pi) is retained explicitly. -/
theorem projObsDual_halfRegularCoordinateLoad (y : L2Z)
    (hy : IsSobolevSeq (1 / 2 : ℝ) (y : FourierSeq)) :
    (Real.sqrt circlePeriod : ℂ) • projObsDual W y =
      cutProj (cutC (W circlePeriod) (basisVec 0))
        (observationAdj W (halfRegularCoordinateLoad y hy : ComplexCurve)) := by
  have h := projObsDual_boundary_normalized hγLip hW (halfRegularCoordinateLoad y hy)
  rw [halfRegularCoordinateLoad_normalized, map_smul] at h
  exact h

private theorem reduced_observationAdj_sub_smul (g r : BoundaryL2) (t : ℂ) :
    observationAdj W ((g - t • r : BoundaryL2) : ComplexCurve) =
      observationAdj W (g : ComplexCurve) - t • observationAdj W (r : ComplexCurve) := by
  have hg := integrable_boundary_observation_load hγLip hW g
  have hr := integrable_boundary_observation_load hγLip hW r
  rw [observationAdj, observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    _ = ∫ θ in Ioc 0 circlePeriod,
        g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0) -
          t • (r θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub g (t • r), Lp.coeFn_smul t r] with θ hs ht
      simp only [hs, ht, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul,
        smul_eq_mul]
    _ = _ := by
      have hsplit := integral_sub hg (hr.smul t)
      simp   at hsplit
      rw [integral_smul] at hsplit
      simpa only [] using hsplit

end


private theorem reduced_eq_smul_of_cutProj_eq_zero
    (c x : Ell2) (h : cutProj c x = 0) :
    x = (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, x⟫_ℂ) • c := by
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at h
  exact sub_eq_zero.mp h

private theorem reduced_injective_of_isUnit
    (B : L2Z →L[ℂ] L2Z) (hB : IsUnit B) : Function.Injective B := by
  obtain ⟨u, rfl⟩ := hB
  intro x y hxy
  have h := congrArg (((↑u⁻¹ : L2Z →L[ℂ] L2Z))) hxy
  simpa  [← ContinuousLinearMap.mul_apply] using h

section PhysicalCoordinates

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

local notation "H₀" => nonpositiveFourierSubspace
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (WithTop.coe_le_coe.mpr le_top))

section
include hb hL hhol hinj hC hK e he hsource hes

/-- For a genuine ordinary coordinate L2 load, zero projected observation
places its normalized load in the actual full nonpositive conormal range.
The radial subtraction is the actual zero-mode H1 Vekua wave. -/
theorem localConformal_projectedObservation_L2_kernel_mem_conormal_range
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    (g : BoundaryL2)
    (hproj : cutProj (cutC (W circlePeriod) (basisVec 0))
      (observationAdj W (g : ComplexCurve)) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧
      NF (E : ℂ) b = sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier g) := by
  let c  := cutC (W circlePeriod) (basisVec 0)
  let α  := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W g⟫_ℂ)
  let t  := -Complex.I * α
  let r  := localConformalRadialCoordinateLoad F hΓLip E 1
  have hspan  :=
    reduced_eq_smul_of_cutProj_eq_zero c _ hproj
  have hrad : observationAdj W (r : ComplexCurve) = Complex.I • c := by
    simpa only [mul_one] using
      localConformalRadialCoordinateLoad_observationAdj F hΓLip hW 1
  have hti : t * Complex.I = α := by
    calc
      (-Complex.I * α) * Complex.I = -(Complex.I * Complex.I) * α := by ring
      _ = α := by rw [Complex.I_mul_I]; ring
  let g₀  := g - t • r
  have hO : observationAdj W (g₀ : ComplexCurve) = 0 := by
    rw [reduced_observationAdj_sub_smul hΓLip hW, hspan, hrad,
      smul_smul, hti, sub_self]
  let b₀  := physicalDrivenKernelInput hΓLip hΓF hW
    g₀ (Lp.memLp g₀) hO
  have hb₀ : IsNonpositiveFourierSupport b₀ :=
    physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource
      hΓLip hE hW g₀ (Lp.memLp g₀) hO
  have hNC₀ : NF (E : ℂ) b₀ = sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier g₀) := by
    have h := physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW
        g₀ (Lp.memLp g₀) hO
    simpa only [physicalDrivenKernelCoordinateLoad, Lp.toLp_coeFn] using h
  have hNCr : NF (E : ℂ) radialVekuaInput =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier r) := by
    simpa only [one_smul, r] using
      localConformalRadial_normalizedConormal_eq_coordinateLoad hR F hFs hb hL hhol hinj
        hC hK e he hsource hes hΓLip hE 1
  refine ⟨b₀ + t • radialVekuaInput, ?_, ?_⟩
  · intro n hn
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      hb₀ n hn, radialVekuaInput_nonpositive n hn, smul_zero, add_zero]
  · rw [map_add, map_smul, hNC₀, hNCr]
    dsimp only [g₀]
    rw [map_sub, map_smul, map_sub, map_smul]
    abel

/-- Half-regular normalized inputs with zero projected observation lie in
the actual conormal range. Regularity is used only to construct their true
ordinary L2 load, not as a substitute for the range identity. -/
theorem localConformal_projectedObservation_half_regular_kernel_mem_conormal_range
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : IsSobolevSeq (1 / 2 : ℝ) (y : FourierSeq))
    (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF (E : ℂ) b = y := by
  have hproj := projObsDual_halfRegularCoordinateLoad hΓLip hW y hy
  rw [hobs, smul_zero] at hproj
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_L2_kernel_mem_conormal_range hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW
        (halfRegularCoordinateLoad y hy) hproj.symm
  exact ⟨b, hbn, hb'.trans (halfRegularCoordinateLoad_normalized y hy)⟩

/-- The true projected observation is injective on half-regular vectors
of an actual fixed complement chart. The chart hypothesis is an actual
unit, rather than the desired reduced injectivity conclusion. -/
theorem localConformal_fixed_complement_half_regular_kernel_eq_zero
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → ComplexEnd Ell2} (hW : IsTransport ΓF E W)
    (T : H₀ᗮ →L[ℂ] L2Z)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      T ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hz : IsSobolevSeq (1 / 2 : ℝ) (T z : FourierSeq))
    (hobs : projObsDual W (T z) = 0) : z = 0 := by
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_half_regular_kernel_mem_conormal_range hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hΓLip hE hW (T z) hz hobs
  let a : H₀ := ⟨b, hbn⟩
  have heq  := hb'.symm
  exact (chart_range_inter_eq_zero H₀ ((NF E).comp (H₀).subtypeL) T
    (reduced_injective_of_isUnit _ hunit) a z heq).1

end


end PhysicalCoordinates

end PolyaNeumann

end
