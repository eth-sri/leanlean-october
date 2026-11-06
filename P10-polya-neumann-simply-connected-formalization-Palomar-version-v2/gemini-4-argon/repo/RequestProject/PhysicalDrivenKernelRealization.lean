module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate ContDiff

variable {γ : ℝ → ℂ} {L : NNReal} {E : ℝ}

local instance drivenRealizationTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem driven_realization_circle_coeff
    (H : C(AddCircle (2 * Real.pi), ℂ)) :
    fourierCoeff H = fourierCoeffOn Real.two_pi_pos
      (fun θ => H (θ : AddCircle (2 * Real.pi))) := by
  funext n
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ => H (θ : AddCircle (2 * Real.pi))) n
  simpa [show AddCircle.liftIoc (2 * Real.pi) 0 (fun θ => H (θ : AddCircle (2 * Real.pi))) = (H : AddCircle (2 * Real.pi) → ℂ) by
    funext q
    change H ((AddCircle.equivIoc (2 * Real.pi) 0 q) :
      AddCircle (2 * Real.pi)) = _
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q) :
        AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]] using h

/-- The actual continuous circle representative of the zeroth driven
gauge. Its matching endpoint values come from the true observation kernel. -/
def physicalDrivenKernelCircleGauge
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
    obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
    exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
      (physicalDrivenGauge_continuousOn γ hγ E _
        (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)⟩

/-- The genuine normalized Hardy input of the driven kernel. The
ordinary averaged coefficient is multiplied by sqrt(2π) sqrt(λ_n). -/
local notation "Φ3" => physicalDrivenPeriodicGauge γ E

local notation "Φ4" => LipschitzWith L γ

local notation "Φ5" => IsTransport γ E

def physicalDrivenKernelInput
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
     {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : Φ5 W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) : L2Z :=
  (Real.sqrt (2 * Real.pi) : ℂ) • sobVec (1 / 2 : ℝ)
    (fourierCoeffOn Real.two_pi_pos (Φ3 W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

theorem physicalDrivenKernelInput_apply
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
      (hW : Φ5 W)
    g hg
    (hO : observationAdj W g = 0) n :
    physicalDrivenKernelInput hγLip hγ hW g hg hO n =
      (Real.sqrt (2 * Real.pi) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        fourierCoeffOn Real.two_pi_pos (Φ3 W g 0) n := by
  simp [physicalDrivenKernelInput, mul_assoc]

theorem fromL2_physicalDrivenKernelInput
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
      (hW : Φ5 W)
    g hg
    (hO : observationAdj W g = 0) :
    fromL2 (1 / 2) (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (Φ3 W g 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

/-- The normalized input has the actual extra half order supplied by
the forced zeroth-row equation, without a regularity premise on g's kernel. -/
theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
     {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : Φ5 W)
    g hg
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2)
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem normalizedHardyAverage_physicalDrivenKernelInput
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
      (hW : Φ5 W)
    g hg
    (hO : observationAdj W g = 0) :
    normalizedHardyAverage (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (Φ3 W g 0) := by
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) = _
  rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ (by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'), one_smul]

/-- The initial Hardy value reconstructed from the derived coefficients
is the actual continuous driven zeroth gauge at every parameter. -/
theorem hardyFourierTrace_physicalDrivenKernelInput
      (hγLip : Φ4) (hγ : ContDiff ℝ 1 γ)
      (hW : Φ5 W)
    g hg
    (hO : observationAdj W g = 0) θ :
    hardyFourierTrace (normalizedHardyAverage
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) θ =
      Φ3 W g 0 θ := by
  let H := physicalDrivenKernelCircleGauge γ hγ.continuous E hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) hO
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (Φ3 W g 0) :=
    driven_realization_circle_coeff _
  rw [normalizedHardyAverage_physicalDrivenKernelInput, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H (by
    rw [hcoef]
    exact (sq_tsum_norm_le (s := 0) (by norm_num)
      (by
        simpa using
          (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO))).1) θ

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
      dsimp only
      rw [ih s ⟨hs.1, hs.2.trans hθ.2⟩]

/-- A genuine boundary L² function with order-one coefficients equals
their continuous Fourier reconstruction a.e. This uses the actual
unitary boundary Fourier transform, without presuming a representative. -/
theorem boundaryL2_ae_hardyFourierTrace_of_H1
    (v : BoundaryL2)
    (hv : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ))) :
    (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      hardyFourierTrace (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)) := by
  let c := fourierCoeffOn Real.two_pi_pos v
  have hc : Summable (fun n => ‖c n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ℝ → ℂ := fun θ => H (θ : AddCircle (2 * Real.pi))
  have hfm : MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ((H.continuous.comp (AddCircle.continuous_mk' _)).continuousOn)
    refine MemLp.of_bound
      ((((H.continuous.comp (AddCircle.continuous_mk' _)).continuousOn).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ =>
      hC θ (Ioc_subset_Icc_self hθ)
  let w : BoundaryL2 := hfm.toLp f
  have haw := hfm.coeFn_toLp
  have hav : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := by
    rw [boundaryFourier.injective (show boundaryFourier v = boundaryFourier w by
      apply lp.ext
      funext n
      rw [boundaryFourier_apply, boundaryFourier_apply, show fourierCoeffOn Real.two_pi_pos w = c by
        rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw]
        change fourierCoeffOn Real.two_pi_pos
          (fun θ => H (θ : AddCircle (2 * Real.pi))) = c
        rw [← driven_realization_circle_coeff, hardyCircleReconstruction_fourierCoeff hc]])]
    exact haw
  filter_upwards [hav] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

theorem normalizedHardyAverage_localConformalDiskHalfTrace
     (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    hL
    u :
    normalizedHardyAverage (localConformalDiskHalfTrace hR F hFs hL u) =
      fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) := by
  funext n
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ (by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'), one_mul]

section PhysicalCoordinates

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
    {L : NNReal} (hγLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)

local notation "hγF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "bF" => physicalDrivenKernelInput hγLip hγF hW g hg hO

include hb hL hhol hC e he hsource hE in
/-- The normalized input of an actual driven observation-kernel vector
lies in the full nonpositive Fourier sector, including its constant mode. -/
theorem physicalDrivenKernelInput_nonpositive : IsNonpositiveFourierSupport bF := by
  intro n hn
  rw [physicalDrivenKernelInput_apply, (localConformal_physicalDrivenGauge_nonpositive_of_memLp hb hL hR F hFs hhol (by
    intro z hz w hw hzw
    apply e.injOn (hsource hz) (hsource hw)
    simpa [he] using hzw) (by
    have hc : ContinuousOn (fun z => C * ‖fderiv ℝ F z 1‖ ^ 2)
        (closedBall 0 1) :=
      (continuousOn_const.mul
        ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
          continuousOn_const).norm).pow 2)).mono (closedBall_subset_ball hR)
    intro z hz hzero
    have hbound : 1 ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := by
      apply le_on_closure (show ∀ z ∈ ball 0 1, 1 ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 by
        intro z hz
        rw [show fderiv ℝ F z 1 = deriv F z by
          rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
          change fderiv ℂ F z 1 = _
          rw [fderiv_eq_deriv_mul, mul_one]]
        exact hC z hz) continuousOn_const
      · simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hc
      · simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
    have hbad : (1 : ℝ) ≤ 0 := by
      simpa [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        using hbound
    norm_num at hbad) rfl hγLip hE hW g hg hO 0) n hn, mul_zero]

/-- The actual interior H¹ vector determined by the driven observation
kernel, centered at the same genuine boundary basepoint F(1). -/
def physicalDrivenKernelH1 : NeumannH1 (F '' ball 0 1) :=
  localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) bF

include hE in
/-- The all-input actual Volterra trace series reconstructs the genuine
driven zeroth row. No zero-trace kernel formula is used in this proof. -/
theorem physicalDrivenKernelH1_trace_reconstruction
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    hardyFourierTrace (normalizedHardyAverage
      (localConformalDiskHalfTrace hR F hFs hL
        (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
          e he hsource hes hγLip hW g hg hO))) θ =
      physicalDrivenRow (physicalDrivenVector W g) 0 θ := by
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E bF (physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource hγLip hE hW g hg hO) (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO) θ
  have hprim j :
      volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage bF)) j θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (physicalDrivenGauge (physicalCircleTrace F) E (physicalDrivenVector W g) 0) j θ := by
    apply driven_realization_volterra_congrOn (T := 2 * Real.pi) ?_ j θ hθ
    intro s hs
    rw [hardyFourierTrace_physicalDrivenKernelInput,
      physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]
  change hardyFourierTrace (normalizedHardyAverage
    (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E bF)) θ = _
  calc
    _ = _ := hs.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro j
      rw [hprim, show F (circleMap 0 1 θ) - F 1 = physicalDrivenCentered (physicalCircleTrace F) θ by
        simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]]
      rfl
    _ = _ := (physicalDrivenRow_eq_volterraVekua_of_nonnegative_of_memLp
      hγLip hγF hE.le hW g hg hθ).symm

include hE in
/-- The actual ordinary coordinate trace of the constructed physical H¹
vector is the actual driven row in boundary L², with its correct scale. -/
theorem physicalDrivenKernelH1_coordinate_trace_ae :
    (localConformalDiskH1Trace hR F hFs hL
      (physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγLip hW g hg hO) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        physicalDrivenRow (physicalDrivenVector W g) 0 := by
  let u := physicalDrivenKernelH1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hW g hg hO
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL u
  change normalizedHardyAverage
      (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E bF) =
    fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) at hcoef
  have htrace := boundaryL2_ae_hardyFourierTrace_of_H1
    (localConformalDiskH1Trace hR F hFs hL u) (by rw [← hcoef]; exact (isSobolevSeq_smul _ (localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK e he hsource hes E bF (physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource hγLip hE hW g hg hO) (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hγLip hγF hW g hg hO))))
  rw [← hcoef] at htrace
  filter_upwards [htrace, ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  exact ht.trans (physicalDrivenKernelH1_trace_reconstruction hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγLip hE hW g hg hO (Ioc_subset_Icc_self hθ))

end PhysicalCoordinates

end PolyaNeumann

end
