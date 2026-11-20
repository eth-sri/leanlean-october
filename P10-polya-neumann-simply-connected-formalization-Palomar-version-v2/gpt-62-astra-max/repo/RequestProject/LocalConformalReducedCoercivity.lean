module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.LocalConformalRadialVekua
public import RequestProject.ObservationLp
public import RequestProject.ReducedForm
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

section

variable (y : L2Z) (hy : IsSobolevSeq halfOrder (y : ℤ → ℂ))
include hy

/-- The genuine ordinary boundary L2 load represented by a half-regular
normalized Fourier vector. -/
def halfRegularCoordinateLoad : BoundaryL2 :=
  boundaryFourier.symm (sobVec halfOrder (y : ℤ → ℂ) hy)

/-- The unitary Fourier normalization is exact, including frequency zero. -/
theorem halfRegularCoordinateLoad_normalized :
    sobolevSmoothing halfOrder (by norm_num)
      (boundaryFourier (halfRegularCoordinateLoad y hy)) = y := by
  rw [halfRegularCoordinateLoad, boundaryFourier.apply_symm_apply]
  apply lp.ext
  funext n
  change fromL2 halfOrder (sobVec halfOrder (y : ℤ → ℂ) hy) n = y n
  rw [fromL2_sobVec]

end

/-- The normalized projected observation agrees with the actual ordinary
L2 observation. The factor sqrt(2 pi) is retained explicitly. -/
theorem projObsDual_halfRegularCoordinateLoad
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ}
    {W : TransportPath} (hγLip : LipschitzWith L γ)
    (hW : IsTransport γ E W) (y : L2Z)
    (hy : IsSobolevSeq halfOrder (y : ℤ → ℂ)) :
    fourierScale • projObsDual W y =
      cutProj (cutVector W)
        (observationAdj W (halfRegularCoordinateLoad y hy : ℝ → ℂ)) := by
  have h := projObsDual_boundary_normalized hγLip hW (halfRegularCoordinateLoad y hy)
  rw [halfRegularCoordinateLoad_normalized, map_smul] at h
  exact h

private theorem reduced_observationAdj_sub_smul
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ}
    {W : TransportPath} (hγLip : LipschitzWith L γ)
    (hW : IsTransport γ E W) (g r : BoundaryL2) (t : ℂ) :
    observationAdj W ((g - t • r : BoundaryL2) : ℝ → ℂ) =
      observationAdj W (g : ℝ → ℂ) - t • observationAdj W (r : ℝ → ℂ) := by
  
  
  rw [observationAdj, observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    _ = ∫ θ in angleIoc,
        g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0) -
          t • (r θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub g (t • r), Lp.coeFn_smul t r] with θ hs ht
      simp only [hs, ht, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul,
        smul_eq_mul]
    _ = _ := by
      have hsplit := integral_sub (integrable_boundary_observation_load hγLip hW g) ((integrable_boundary_observation_load hγLip hW r).smul t)
      simp at hsplit
      rw [integral_smul] at hsplit
      exact hsplit

private theorem reduced_eq_smul_of_cutProj_eq_zero
    (c x : Ell2) (h : cutProj c x = 0) :
    x = (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, x⟫_ℂ) • c := by
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at h
  exact sub_eq_zero.mp h

private theorem reduced_injective_of_isUnit
    (B : FourierOp) (hB : IsUnit B) : Function.Injective B := by
  obtain ⟨u, rfl⟩ := hB
  intro x y hxy
  have h := congrArg ((↑u⁻¹ : FourierOp)) hxy
  simpa only [← ContinuousLinearMap.mul_apply, Units.inv_mul,
    ContinuousLinearMap.one_apply] using h

section PhysicalCoordinates

section

variable (Φ : DiskCoordinates)

/-- For a genuine ordinary coordinate L2 load, zero projected observation
places its normalized load in the actual full nonpositive conormal range.
The radial subtraction is the actual zero-mode H1 Vekua wave. -/
theorem localConformal_projectedObservation_L2_kernel_mem_conormal_range {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : BoundaryL2)
    (hproj : cutProj (cutVector W)
      (observationAdj W (g : ℝ → ℂ)) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧
      Φ.conormal (E : ℂ) b = sobolevSmoothing halfOrder (by norm_num)
        (boundaryFourier g) := by
  let c  := cutVector W
  let α  := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W (g : ℝ → ℂ)⟫_ℂ)
  let t  := -Complex.I * α
  let r  := localConformalRadialCoordinateLoad Φ.map hΓLip E 1
  have hspan  :=
    reduced_eq_smul_of_cutProj_eq_zero c _ hproj
  have hrad : observationAdj W (r : ℝ → ℂ) = Complex.I • c := by
    simpa only [r, c, mul_one] using
      localConformalRadialCoordinateLoad_observationAdj Φ.map hΓLip hW (1 : ℂ)
  have hti : t * Complex.I = α := by
    dsimp only [t]
    calc
      _ = -(Complex.I * Complex.I) * α := by ring
      _ = α := by simp
  let g₀  := g - t • r
  have hO : observationAdj W g₀ = 0 := by
    dsimp only [g₀]
    rw [reduced_observationAdj_sub_smul hΓLip hW, (reduced_eq_smul_of_cutProj_eq_zero c _ hproj), hrad,
      smul_smul, hti, sub_self]
  let b₀  := physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW
    (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
  have hb₀ : IsNonpositiveFourierSupport b₀ :=
    physicalDrivenKernelInput_nonpositive Φ Φ.bounded Φ.lipschitzDomain Φ.holomorphic Φ.deriv_lower Φ.chart Φ.chart_eq Φ.source
      hΓLip hE hW (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
  have hNC₀ : Φ.conormal (E : ℂ) b₀ = sobolevSmoothing halfOrder (by norm_num)
      (boundaryFourier g₀) := by
    have h := physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad Φ hΓLip hE hW
        (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
    simpa [b₀, physicalDrivenKernelCoordinateLoad] using h
  have hNCr : Φ.conormal (E : ℂ) radialVekuaInput =
      sobolevSmoothing halfOrder (by norm_num) (boundaryFourier r) := by
    simpa only [one_smul, r] using
      localConformalRadial_normalizedConormal_eq_coordinateLoad Φ hΓLip hE (1 : ℂ)
  refine ⟨b₀ + t • radialVekuaInput, ?_, ?_⟩
  · intro n hn
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      hb₀ n hn, radialVekuaInput_nonpositive n hn, smul_zero, add_zero]
  · rw [map_add, map_smul, hNC₀, hNCr]
    dsimp [g₀]
    rw [map_sub, map_smul, map_sub, map_smul]
    abel

/-- Half-regular normalized inputs with zero projected observation lie in
the actual conormal range. Regularity is used only to construct their true
ordinary L2 load, not as a substitute for the range identity. -/
theorem localConformal_projectedObservation_half_regular_kernel_mem_conormal_range {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (y : L2Z)
    (hy : IsSobolevSeq halfOrder (y : ℤ → ℂ)) (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ Φ.conormal (E : ℂ) b = y := by
  have hproj := projObsDual_halfRegularCoordinateLoad hΓLip hW y hy
  rw [hobs, smul_zero] at hproj
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_L2_kernel_mem_conormal_range Φ hΓLip hE hW
        (halfRegularCoordinateLoad y hy) hproj.symm
  exact ⟨b, hbn, hb'.trans (halfRegularCoordinateLoad_normalized y hy)⟩

/-- The true projected observation is injective on half-regular vectors
of an actual fixed complement chart. The chart hypothesis is an actual
unit, rather than the desired reduced injectivity conclusion. -/
theorem localConformal_fixed_complement_half_regular_kernel_eq_zero {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (T : nonpositiveFourierSubspaceᗮ →L[ℂ] L2Z)
    (hunit : IsUnit ((Φ.conormal (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL ∘L nonpositiveFourierSubspace.orthogonalProjection +
      T ∘L nonpositiveFourierSubspaceᗮ.orthogonalProjection))
    (z : nonpositiveFourierSubspaceᗮ) (hz : IsSobolevSeq halfOrder (T z : ℤ → ℂ))
    (hobs : projObsDual W (T z) = 0) : z = 0 := by
  obtain ⟨b, hbn, hb'⟩ :=
    localConformal_projectedObservation_half_regular_kernel_mem_conormal_range Φ hΓLip hE hW (T z) hz hobs
  let a : nonpositiveFourierSubspace := ⟨b, hbn⟩
  have heq  := hb'.symm
  exact (chart_range_inter_eq_zero nonpositiveFourierSubspace ((Φ.conormal (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL) T
    (reduced_injective_of_isUnit _ hunit) a z heq).1

end

end PhysicalCoordinates

end PolyaNeumann

end
