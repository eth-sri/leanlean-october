module

public import RequestProject.LocalConformalVekuaConormalBridge


public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalDrivenL2Reconstruction
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.PhysicalVolterraNormalization

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate



/-- The actual continuous circle representative of the zeroth driven
gauge. Its matching endpoint values come from the true observation kernel. -/
def physicalDrivenKernelCircleGauge
    (γ : ComplexCurve) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → ComplexEnd Ell2} (hW : ContinuousOn W boundaryInterval)
    (g : ComplexCurve) (hg : IntervalIntegrable g volume 0 circlePeriod)
    (hO : observationAdj W g = 0) : C(AddCircle circlePeriod, ℂ) :=
  ⟨AddCircle.liftIco circlePeriod 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
    obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
    exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
      (physicalDrivenGauge_continuousOn γ hγ E _
        (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)⟩

theorem physicalDrivenKernelCircleGauge_fourierCoeff
    γ hγ E
     hW
    g hg
    (hO : observationAdj W g = 0) :
    fourierCoeff (physicalDrivenKernelCircleGauge γ hγ E hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
  common_bridge_circle_coeff _

/-- The genuine normalized Hardy input of the driven kernel. The
ordinary averaged coefficient is multiplied by sqrt(2π) sqrt(λ_n). -/
def physicalDrivenKernelInput
    {γ : ComplexCurve} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → ComplexEnd Ell2} (hW : IsTransport γ E W)
    (g : ComplexCurve) (hg : MemLp g 2 (volume.restrict boundaryHalfOpenInterval))
    (hO : observationAdj W g = 0) : L2Z :=
  (Real.sqrt circlePeriod : ℂ) • sobVec (1 / 2 : ℝ)
    (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

section
variable {γ : ComplexCurve}
include γ

section
variable {L } (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ) {E } {W } (hW : IsTransport γ E W) (g ) (hg : MemLp g 2 (volume.restrict boundaryHalfOpenInterval)) (hO : observationAdj W g = 0)
local notation "kernelInputFixed" => physicalDrivenKernelInput hγLip hγ hW g hg hO

local notation "periodicGaugeFixed" => physicalDrivenPeriodicGauge γ E W g

include L hγLip hγ E W hW g hg hO

theorem physicalDrivenKernelInput_apply (n : ℤ) :
    kernelInputFixed n =
      (Real.sqrt circlePeriod : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        fourierCoeffOn Real.two_pi_pos (periodicGaugeFixed 0) n := by
  simp  [physicalDrivenKernelInput, mul_assoc]

theorem fromL2_physicalDrivenKernelInput :
    fromL2 (1 / 2 : ℝ) kernelInputFixed =
      (Real.sqrt circlePeriod : ℂ) •
        fourierCoeffOn Real.two_pi_pos (periodicGaugeFixed 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

/-- The normalized input has the actual extra half order supplied by
the forced zeroth-row equation, without a regularity premise on g's kernel. -/
theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ)
      kernelInputFixed) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem normalizedHardyAverage_physicalDrivenKernelInput :
    normalizedHardyAverage kernelInputFixed =
      fourierCoeffOn Real.two_pi_pos (periodicGaugeFixed 0) := by
  have hs : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  change (Real.sqrt circlePeriod : ℂ)⁻¹ •
      fromL2 (1 / 2) kernelInputFixed = _
  rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The initial Hardy value reconstructed from the derived coefficients
is the actual continuous driven zeroth gauge at every parameter. -/
theorem hardyFourierTrace_physicalDrivenKernelInput θ :
    hardyFourierTrace (normalizedHardyAverage
      kernelInputFixed) θ =
      periodicGaugeFixed 0 θ := by
  let H := physicalDrivenKernelCircleGauge γ hγ.continuous E hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) hO
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (periodicGaugeFixed 0) :=
    physicalDrivenKernelCircleGauge_fourierCoeff _ _ _ _ _ _ _
  have hsum : Summable (fun n => ‖fourierCoeff H n‖) := by
    rw [hcoef]
    have hreg : IsSobolevSeq (0 + 1 : ℝ)
        (fourierCoeffOn Real.two_pi_pos (periodicGaugeFixed 0)) := by
      simpa   using
        (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)
    exact (sq_tsum_norm_le (s := 0) (by norm_num)
      hreg).1
  rw [normalizedHardyAverage_physicalDrivenKernelInput, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H hsum θ

end


end


private theorem driven_realization_volterra_congrOn
      (he : EqOn h k (Icc 0 T)) :
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
    (hv : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (v : ComplexCurve))) :
    (v : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      hardyFourierTrace (fourierCoeffOn Real.two_pi_pos (v : ComplexCurve)) := by
  let c := fourierCoeffOn Real.two_pi_pos v
  have hc  :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ComplexCurve := fun θ => H θ
  have hfc  := H.continuous.comp (AddCircle.continuous_mk' _)
  have hfm := driven_realization_continuousOn_memLp hfc.continuousOn
  let w  := hfm.toLp f
  have haw : (w : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f := hfm.coeFn_toLp
  have hcoef : fourierCoeffOn Real.two_pi_pos (w : ComplexCurve) = c := by
    rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw]
    change fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => H θ) = c
    rw [← common_bridge_circle_coeff, hardyCircleReconstruction_fourierCoeff hc]
  have hF : boundaryFourier v = boundaryFourier w := by
    apply lp.ext
    funext n
    rw [boundaryFourier_apply, boundaryFourier_apply, hcoef]
  have he  := boundaryFourier.injective hF
  have hav : (v : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f := by
    rw [he]
    exact haw
  filter_upwards [hav] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

theorem normalizedHardyAverage_localConformalDiskHalfTrace
     hR F
    (hFs : RealSmoothOnBall F R)
    hL
    u :
    normalizedHardyAverage (localConformalDiskHalfTrace hR F hFs hL u) =
      fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) := by
  have hs : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  funext n
  change (Real.sqrt circlePeriod : ℂ)⁻¹ *
    fromL2 (1 / 2) (localConformalDiskHalfTrace hR F hFs hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

private theorem driven_realization_closed_deriv_ne_zero
     (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C) :
    ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0 := by
  have hc : ContinuousOn (fun z => C * ‖fderiv ℝ F z 1‖ ^ 2)
      closedUnitDisk :=
    (continuousOn_const.mul
      ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
        continuousOn_const).norm).pow 2)).mono (closedBall_subset_ball hR)
  have hle : ∀ z ∈ unitDisk, (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := by
    intro z hz
    have hfd : fderiv ℝ F z 1 = deriv F z := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
      rfl
    rw [hfd]
    exact hC z hz
  intro z hz hzero
  have hbound : (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := by
    apply le_on_closure hle continuousOn_const
    · simpa  [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hc
    · simpa  [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
  have hbad : (1 : ℝ) ≤ 0 := by
    simp_all
  norm_num at hbad

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
    {L } (hγLip : LipschitzWith L (physicalCircleTrace F))
    {E } (hE : 0 < E)
    {W } (hW : IsTransport (physicalCircleTrace F) E W)
    (g ) (hg : MemLp g 2 (volume.restrict boundaryHalfOpenInterval))
    (hO : observationAdj W g = 0)
local notation "vekuaBoundaryFixed" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes


local notation "hγF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "bF" => physicalDrivenKernelInput hγLip hγF hW g hg hO

include hb hL hhol hC e he hsource hE in
/-- The normalized input of an actual driven observation-kernel vector
lies in the full nonpositive Fourier sector, including its constant mode. -/
theorem physicalDrivenKernelInput_nonpositive : IsNonpositiveFourierSupport bF := by
  have hinjc : InjOn F closedUnitDisk := by
    intro z hz w hw hzw
    apply e.injOn (hsource hz) (hsource hw)
    simpa  [he] using hzw
  have hs := localConformal_physicalDrivenGauge_nonpositive_of_memLp hb hL hR F hFs
    hhol hinjc (driven_realization_closed_deriv_ne_zero hR F hFs hhol hC) rfl
    hγLip hE hW g hg hO 0
  simp_all [physicalDrivenKernelInput_apply, PolyaNeumann.IsNonpositiveFourierSupport]

/-- The actual interior H¹ vector determined by the driven observation
kernel, centered at the same genuine boundary basepoint F(1). -/
def physicalDrivenKernelH1  :=
  localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) bF
local notation "kernelH1Fixed" => physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes hγLip hW g hg hO


include hE in
/-- The all-input actual Volterra trace series reconstructs the genuine
driven zeroth row. No zero-trace kernel formula is used in this proof. -/
theorem physicalDrivenKernelH1_trace_reconstruction
     (hθ : θ ∈ boundaryInterval) :
    hardyFourierTrace (normalizedHardyAverage
      (localConformalDiskHalfTrace hR F hFs hL
        kernelH1Fixed)) θ =
      physicalDrivenRow (physicalDrivenVector W g) 0 θ := by
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hγLip hE hW g hg hO
  have hreg := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E bF hbn hreg θ
  have hprim j :
      volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage bF)) j θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (physicalDrivenGauge (physicalCircleTrace F) E (physicalDrivenVector W g) 0) j θ := by
    apply driven_realization_volterra_congrOn (T := 2 * Real.pi) ?_ j θ hθ
    intro s hs
    rw [hardyFourierTrace_physicalDrivenKernelInput,
      physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]
  have hcenter : F (unitCircleMap θ) - F 1 =
      physicalDrivenCentered (physicalCircleTrace F) θ := by
    simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]
  change hardyFourierTrace (normalizedHardyAverage
    (vekuaBoundaryFixed E bF)) θ = _
  calc
    _ = ∑' j : ℕ, physicalVekuaCoeff E j *
        (F (unitCircleMap θ) - F 1) ^ j *
        volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (normalizedHardyAverage bF)) j θ := hs.tsum_eq.symm
    _ = ∑' j : ℕ, (-E / 4) ^ j / j.factorial *
        physicalDrivenCentered (physicalCircleTrace F) θ ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (physicalDrivenGauge (physicalCircleTrace F) E (physicalDrivenVector W g) 0) j θ := by
      measurability
    _ = _ := (physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_memLp
      hγLip hγF hE.le hW g hg hθ).symm

include hE in
/-- The actual ordinary coordinate trace of the constructed physical H¹
vector is the actual driven row in boundary L², with its correct scale. -/
theorem physicalDrivenKernelH1_coordinate_trace_ae :
    (localConformalDiskH1Trace hR F hFs hL
      kernelH1Fixed : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        physicalDrivenRow (physicalDrivenVector W g) 0 := by
  let u := kernelH1Fixed
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hγLip hE hW g hg hO
  have hraw := localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E bF hbn
    (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO)
  have havg : IsSobolevSeq 1 (normalizedHardyAverage
      (vekuaBoundaryFixed (E : ℂ) bF)) := isSobolevSeq_smul _ hraw
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL u
  change normalizedHardyAverage
      (vekuaBoundaryFixed E bF) =
    fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) at hcoef
  have htrace := boundaryL2_ae_hardyFourierTrace_of_H1
    (localConformalDiskH1Trace hR F hFs hL u) (by rw [← hcoef]; exact havg)
  rw [← hcoef] at htrace
  filter_upwards [htrace, ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  exact ht.trans (physicalDrivenKernelH1_trace_reconstruction hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hE hW g hg hO (Ioc_subset_Icc_self hθ))

end PhysicalCoordinates

end PolyaNeumann

end
