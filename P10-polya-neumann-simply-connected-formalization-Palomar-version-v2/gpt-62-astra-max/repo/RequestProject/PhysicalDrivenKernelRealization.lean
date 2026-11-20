module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalDrivenL2Reconstruction
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.PhysicalVolterraNormalization
public import RequestProject.PlanarNotation

/-!
# Genuine H¹ realization of the driven observation kernel

The actual zeroth factorial gauge of an L² driven vector determines
normalized Hardy input, with the ordinary `sqrt(2π)` Fourier scale.
Its regularity is supplied by the proved forced zeroth-row equation,
and its Fourier support by the actual physical moment criterion.
The physical H¹ Vekua series is centered at F(1), including mode zero.

This module is part of the verified dependency chain. Initial
conformal-coordinate existence and identification of the final physical
normal load remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

section

variable (γ : ℝ → ℂ) (Φ : SmoothDiskMap) (hγ : Continuous γ) (E : ℝ)

include E hγ in
/-- The actual continuous circle representative of the zeroth driven
gauge. Its matching endpoint values come from the true observation kernel. -/
def physicalDrivenKernelCircleGauge
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    (hO : observationAdj W g = 0) : C(ParamCircle, ℂ) :=
  ⟨AddCircle.liftIco anglePeriod 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
    obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
    exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
      (physicalDrivenGauge_continuousOn γ hγ E _
        (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)⟩

theorem physicalDrivenKernelCircleGauge_fourierCoeff
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    (hO : observationAdj W g = 0) :
    fourierCoeff (physicalDrivenKernelCircleGauge γ hγ E hW g hg hO) =
      angleCoeff (physicalDrivenPeriodicGauge γ E W g 0) :=
  circle_fourierCoeff_eq _

/-- The genuine normalized Hardy input of the driven kernel. The
ordinary averaged coefficient is multiplied by sqrt(2π) sqrt(λ_n). -/
def physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) : L2Z :=
  fourierScale • sobVec halfOrder
    (angleCoeff (physicalDrivenPeriodicGauge γ E W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

theorem physicalDrivenKernelInput_apply
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) (n : ℤ) :
    physicalDrivenKernelInput hγLip hγ hW g hg hO n =
      fourierScale * ((sobWeight n ^ halfOrder : ℝ) : ℂ) *
        angleCoeff (physicalDrivenPeriodicGauge γ E W g 0) n := by
  simp [physicalDrivenKernelInput, mul_assoc]

theorem fromL2_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    fromL2 halfOrder (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      fourierScale •
        angleCoeff (physicalDrivenPeriodicGauge γ E W g 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

/-- The normalized input has the actual extra half order supplied by
the forced zeroth-row equation, without a regularity premise on g's kernel. -/
theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fromL2 halfOrder
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem normalizedHardyAverage_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    normalizedHardyAverage (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      angleCoeff (physicalDrivenPeriodicGauge γ E W g 0) := by
  
  change (Real.sqrt anglePeriod : ℂ)⁻¹ •
      fromL2 halfOrder (physicalDrivenKernelInput hγLip hγ hW g hg hO) = _
  rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ (by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'), one_smul]

/-- The initial Hardy value reconstructed from the derived coefficients
is the actual continuous driven zeroth gauge at every parameter. -/
theorem hardyFourierTrace_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) θ =
      physicalDrivenPeriodicGauge γ E W g 0 θ := by
  let H := physicalDrivenKernelCircleGauge γ hγ.continuous E hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) hO
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
    physicalDrivenKernelCircleGauge_fourierCoeff _ _ _ _ _ _ _
  have hsum : Summable (fun n => ‖fourierCoeff H n‖) := by
    rw [hcoef]
    
    refine (sq_tsum_norm_le (s := 0) (by norm_num)
      ?_).1
    simpa only [zero_add] using
      (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)
  rw [normalizedHardyAverage_physicalDrivenKernelInput, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H hsum θ

private theorem driven_realization_volterra_congrOn
    {a h k : ℝ → ℂ} {T : ℝ} (he : EqOn h k (Icc 0 T)) :
    ∀ j θ, θ ∈ Icc 0 T →
      volterraPrimitiveIterate a h j θ = volterraPrimitiveIterate a k j θ := by
  intro j
  induction j with
  | zero => exact he
  | succ j ih =>
      intro θ hθ
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      
      grind

/-- A genuine boundary L² function with order-one coefficients equals
their continuous Fourier reconstruction a.e. This uses the actual
unitary boundary Fourier transform, without presuming a representative. -/
theorem boundaryL2_ae_hardyFourierTrace_of_H1
    (v : BoundaryL2)
    (hv : IsSobolevSeq 1 (angleCoeff (v : ℝ → ℂ))) :
    (v : ℝ → ℂ) =ᵐ[angleMeasure]
      hardyFourierTrace (angleCoeff (v : ℝ → ℂ)) := by
  let c := fourierCoeffOn Real.two_pi_pos v
  have hc  :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ℝ → ℂ := fun θ => H θ
  
  have hfm := memLp_angle_of_continuousOn (H.continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  let w  := hfm.toLp f
  have haw : w =ᵐ[angleMeasure] f := hfm.coeFn_toLp
  have hcoef : fourierCoeffOn Real.two_pi_pos w = c := by
    rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw, ← circle_fourierCoeff_eq, hardyCircleReconstruction_fourierCoeff hc]
  have hF : boundaryFourier v = boundaryFourier w := by
    ext n
    rw [boundaryFourier_apply, boundaryFourier_apply, hcoef]
  
  have hav : v =ᵐ[angleMeasure] f := by
    rw [(boundaryFourier.injective hF)]
    exact haw
  filter_upwards [hav] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

theorem normalizedHardyAverage_localConformalDiskHalfTrace
    (hL : IsLipschitzDomain Φ.domain) (u : NeumannH1 Φ.domain) :
    normalizedHardyAverage (Φ.pulledBackHalfTrace hL u) =
      angleCoeff (Φ.pulledBackTrace hL u) := by
  
  funext n
  change (Real.sqrt anglePeriod : ℂ)⁻¹ *
    fromL2 halfOrder (Φ.pulledBackHalfTrace hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ (by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'), one_mul]

private theorem driven_realization_closed_deriv_ne_zero {C : ℝ}
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv Φ.map z‖ ^ 2) :
    ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0 := by
  have hc : ContinuousOn (fun z => C * ‖fderiv ℝ Φ.map z 1‖ ^ 2)
      closedDisk :=
    (continuousOn_const.mul
      ((((Φ.smooth.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
        continuousOn_const).norm).pow 2)).mono (closedBall_subset_ball Φ.one_lt_radius)
  have hle : ∀ z ∈ unitDisk, 1 ≤ C * ‖fderiv ℝ Φ.map z 1‖ ^ 2 := by
    intro z hz
    have hfd : fderiv ℝ Φ.map z 1 = deriv Φ.map z := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
      rfl
    simp [*]
  intro z hz hzero
  have hbound : 1 ≤ C * ‖fderiv ℝ Φ.map z 1‖ ^ 2 := by
    apply le_on_closure hle continuousOn_const
    · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hc
    · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa only [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      using hbound
  norm_num at hbad

end

section PhysicalCoordinates

section

variable (Φ : DiskCoordinates)

/-- The normalized input of an actual driven observation-kernel vector
lies in the full nonpositive Fourier sector, including its constant mode. -/
theorem physicalDrivenKernelInput_nonpositive (Φ : SmoothDiskMap) {C : ℝ}
    (hb : Bornology.IsBounded Φ.domain) (hL : IsLipschitzDomain Φ.domain)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv Φ.map z‖ ^ 2)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    {L : NNReal} (hγLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E)
    {W : TransportPath} (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ)
    (hg : MemLp g 2 angleMeasure) (hO : observationAdj W g = 0) : IsNonpositiveFourierSupport (physicalDrivenKernelInput hγLip Φ.boundaryC1 hW g hg hO) := by
  
  have hs := localConformal_physicalDrivenGauge_nonpositive_of_memLp hb hL Φ hhol (by
      intro z hz w hw hzw
      apply e.injOn (hsource hz) (hsource hw)
      simpa [he] using hzw) (driven_realization_closed_deriv_ne_zero Φ hhol hC) rfl
    hγLip hE hW g hg hO 0
  intro n hn
  rw [physicalDrivenKernelInput_apply, hs n hn, mul_zero]

/-- The actual interior H¹ vector determined by the driven observation
kernel, centered at the same genuine boundary basepoint F(1). -/
def physicalDrivenKernelH1 {L : NNReal}
    (hγLip : LipschitzWith L Φ.boundary) {E : ℝ} {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) : NeumannH1 Φ.domain :=
  Φ.vekuaH1AtBoundaryOrigin (E : ℂ) (physicalDrivenKernelInput hγLip Φ.boundaryC1 hW g hg hO)

/-- The all-input actual Volterra trace series reconstructs the genuine
driven zeroth row. No zero-trace kernel formula is used in this proof. -/
theorem physicalDrivenKernelH1_trace_reconstruction {L : NNReal}
    (hγLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    hardyFourierTrace (normalizedHardyAverage
      (Φ.pulledBackHalfTrace Φ.lipschitzDomain
        (physicalDrivenKernelH1 Φ hγLip hW g hg hO))) θ =
      physicalDrivenRow (physicalDrivenVector W g) 0 θ := by
  
  
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 Φ E (physicalDrivenKernelInput hγLip Φ.boundaryC1 hW g hg hO) (physicalDrivenKernelInput_nonpositive Φ Φ.bounded Φ.lipschitzDomain Φ.holomorphic Φ.deriv_lower
    Φ.chart Φ.chart_eq Φ.source hγLip hE hW g hg hO) (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip Φ.boundaryC1 hW g hg hO) θ
  have hprim (j : ℕ) :
      volterraPrimitiveIterate (fun s => star (deriv Φ.boundary s))
        (hardyFourierTrace (normalizedHardyAverage (physicalDrivenKernelInput hγLip Φ.boundaryC1 hW g hg hO))) j θ =
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (physicalDrivenGauge Φ.boundary E (physicalDrivenVector W g) 0) j θ := by
    apply driven_realization_volterra_congrOn  ?_ j θ hθ
    intro s hs
    rw [hardyFourierTrace_physicalDrivenKernelInput,
      physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]
  have hcenter : Φ.map (unitCirclePt θ) - Φ.map 1 =
      physicalDrivenCentered Φ.boundary θ := by
    simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]
  
  calc
    _ = _ := hs.tsum_eq.symm
    _ = ∑' j : ℕ, (-E / 4) ^ j / j.factorial *
        physicalDrivenCentered Φ.boundary θ ^ j *
        volterraPrimitiveIterate _
          _ j θ := by
      apply tsum_congr
      intro j
      rw [hprim, hcenter]
      rfl
    _ = _ := (physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_memLp
      hγLip Φ.boundaryC1 hE.le hW g hg hθ).symm

/-- The actual ordinary coordinate trace of the constructed physical H¹
vector is the actual driven row in boundary L², with its correct scale. -/
theorem physicalDrivenKernelH1_coordinate_trace_ae {L : NNReal}
    (hγLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    (Φ.pulledBackTrace Φ.lipschitzDomain
      (physicalDrivenKernelH1 Φ hγLip hW g hg hO) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        physicalDrivenRow (physicalDrivenVector W g) 0 := by
  let u := physicalDrivenKernelH1 Φ hγLip hW g hg hO
  have hbn := physicalDrivenKernelInput_nonpositive Φ Φ.bounded Φ.lipschitzDomain Φ.holomorphic Φ.deriv_lower
    Φ.chart Φ.chart_eq Φ.source hγLip hE hW g hg hO
  have hraw := localConformalVekuaBoundary_raw_H1 Φ (E : ℂ) _ hbn
    (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip Φ.boundaryC1 hW g hg hO)
  
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace Φ Φ.lipschitzDomain u
  
  have htrace := boundaryL2_ae_hardyFourierTrace_of_H1
    (Φ.pulledBackTrace Φ.lipschitzDomain u) (by rw [← hcoef]; exact (isSobolevSeq_smul _ hraw))
  rw [← hcoef] at htrace
  filter_upwards [htrace, ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  exact ht.trans (physicalDrivenKernelH1_trace_reconstruction Φ hγLip hE hW g hg hO (Ioc_subset_Icc_self hθ))

end

end PhysicalCoordinates

end PolyaNeumann

end
