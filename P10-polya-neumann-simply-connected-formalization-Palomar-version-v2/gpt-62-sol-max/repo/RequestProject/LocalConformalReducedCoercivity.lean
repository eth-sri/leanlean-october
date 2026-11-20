module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.LocalConformalVekuaForward
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

section

variable {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
include γ L E W hγLip hW

/-- The normalized projected observation agrees with the actual ordinary
L2 observation. The factor sqrt(2 pi) is retained explicitly. -/
theorem projObsDual_halfRegularCoordinateLoad
     (y : L2Z)
    (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ)) :
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W y =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (halfRegularCoordinateLoad y hy : ℝ → ℂ)) := by
  have h := projObsDual_boundary_normalized hγLip hW (halfRegularCoordinateLoad y hy)
  rw [halfRegularCoordinateLoad_normalized, map_smul] at h
  assumption

private theorem reduced_observationAdj_sub_smul
     (g r : BoundaryL2) (t : ℂ) :
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
      simp only [hs, ht, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul,
        smul_eq_mul]
    _ = _ := by
      have hsplit := integral_sub hg (hr.smul t)
      simp  [Pi.smul_apply] at hsplit
      rw [integral_smul] at hsplit
      assumption

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
  have h := congrArg (fun z : L2Z => (↑u⁻¹ : L2Z →L[ℂ] L2Z) z) hxy
  simpa only [← ContinuousLinearMap.mul_apply, Units.inv_mul,
    ContinuousLinearMap.one_apply] using h

/-- Normalized half-trace input for the actual ordinary Hardy constant one. -/
def radialVekuaInput : L2Z := (Real.sqrt (2 * Real.pi) : ℂ) • stdBasisZ 0

theorem radialVekuaInput_apply (n : ℤ) :
    radialVekuaInput n = if n = 0 then (Real.sqrt (2 * Real.pi) : ℂ) else 0 := by
  by_cases hn : n = 0
  simp_all [radialVekuaInput, stdBasisZ_apply]
  simp [radialVekuaInput, stdBasisZ_apply, hn]

theorem radialVekuaInput_nonpositive : IsNonpositiveFourierSupport radialVekuaInput := by
  intro n hn
  grind [radialVekuaInput_apply]

theorem normalizedHardyAverage_radialVekuaInput (n : ℤ) :
    normalizedHardyAverage radialVekuaInput n = if n = 0 then 1 else 0 := by
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  by_cases hn : n = 0
  · subst n
    simp only [normalizedHardyAverage, fromL2, radialVekuaInput_apply,
      sobWeight, Int.cast_zero, abs_zero]
    norm_num
    have h2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
      simp
    have hπ : (Real.sqrt (Real.pi) : ℂ) ≠ 0 := by
      simp_all
    grind
  simp [normalizedHardyAverage, fromL2, radialVekuaInput_apply, hn]

theorem radialVekuaInput_half : IsSobolevSeq (1 / 2 : ℝ) (radialVekuaInput : ℤ → ℂ) := by
  classical
  unfold IsSobolevSeq
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := by simp_all
  simp [radialVekuaInput_apply, hn0]

theorem hardyFourierTrace_radialVekuaInput (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage radialVekuaInput) θ = 1 := by simp [hardyFourierTrace, normalizedHardyAverage_radialVekuaInput]

section PhysicalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "H₀" => nonpositiveFourierSubspace
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "NF" => normalizedConormal hβF haF hgF
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
  (coords.smooth.of_le (WithTop.coe_le_coe.mpr le_top))

/-- For a genuine ordinary coordinate L2 load, zero projected observation
places its normalized load in the actual full nonpositive conormal range.
The radial subtraction is the actual zero-mode H1 Vekua wave. -/
theorem localConformal_projectedObservation_L2_kernel_mem_conormal_range
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (g : BoundaryL2)
    (hproj : cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
      (observationAdj W (g : ℝ → ℂ)) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧
      NF (E : ℂ) b = sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier g) := by
  let c := cutC (W (2 * Real.pi)) (basisVec 0)
  let α := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W (g : ℝ → ℂ)⟫_ℂ)
  let t := -Complex.I * α
  let r := localConformalVekuaForwardLoad coords (E : ℂ) radialVekuaInput radialVekuaInput_half
  have hspan :=
    reduced_eq_smul_of_cutProj_eq_zero c _ hproj
  have hrad : observationAdj W (r : ℝ → ℂ) = Complex.I • c := by
    simpa only [r, c, hardyFourierTrace_radialVekuaInput, mul_one] using
      localConformalVekuaForward_observationAdj_eq_cut coords E hE.le radialVekuaInput
        radialVekuaInput_nonpositive radialVekuaInput_half hΓLip hW
  have hti : t * Complex.I = α := by
    dsimp  [t]
    calc
      (-Complex.I * α) * Complex.I = -(Complex.I * Complex.I) * α := by ring
      _ = α := by simp
  let g₀ := g - t • r
  have hO : observationAdj W (g₀ : ℝ → ℂ) = 0 := by
    dsimp only [g₀]
    rw [reduced_observationAdj_sub_smul hΓLip hW, hspan, hrad,
      smul_smul, hti, sub_self]
  obtain ⟨b₀, hb₀, hNC₀⟩ := conormal_eq_of_observationAdj_eq_zero coords hΓLip hE hW g₀ hO
  have hNCr : NF (E : ℂ) radialVekuaInput =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier r) := by
    exact (localConformalVekuaForwardLoad_normalized coords
      (E : ℂ) radialVekuaInput radialVekuaInput_half).symm
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
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ))
    (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF (E : ℂ) b = y := by
  have hproj := projObsDual_halfRegularCoordinateLoad hΓLip hW y hy
  rw [hobs, smul_zero] at hproj
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_L2_kernel_mem_conormal_range coords hΓLip hE hW
        (halfRegularCoordinateLoad y hy) hproj.symm
  exact ⟨b, hbn, hb'.trans (halfRegularCoordinateLoad_normalized y hy)⟩

/-- The true projected observation is injective on half-regular vectors
of an actual fixed complement chart. The chart hypothesis is an actual
unit, rather than the desired reduced injectivity conclusion. -/
theorem localConformal_fixed_complement_half_regular_kernel_eq_zero
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (T : H₀ᗮ →L[ℂ] L2Z)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      T ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hz : IsSobolevSeq (1 / 2 : ℝ) (T z : ℤ → ℂ))
    (hobs : projObsDual W (T z) = 0) : z = 0 := by
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_half_regular_kernel_mem_conormal_range coords hΓLip hE hW (T z) hz hobs
  let a : H₀ := ⟨b, hbn⟩
  have heq := hb'.symm
  exact (chart_range_inter_eq_zero H₀ ((NF (E : ℂ)).comp (H₀).subtypeL) T
    (reduced_injective_of_isUnit _ hunit) a z heq).1

end PhysicalCoordinates

end PolyaNeumann

end
