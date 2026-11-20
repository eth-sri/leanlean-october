module

public import RequestProject.CircleFourier
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.LocalConformalHerglotz
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.HerglotzReduction
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardySupport
public import RequestProject.KernelFourierAction
public import RequestProject.NormalizedPeriodicRegular
public import Mathlib.MeasureTheory.Integral.Prod
public import RequestProject.Reparam

/-! The Fourier and integral representations of the periodic boundary kernels,
and the ordinary traces and conormal loads of Herglotz waves. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric Real Filter
open scoped Real InnerProductSpace ComplexConjugate

/-- The actual conormal derivative obeys the Jacobian law a.e. for the
supplied C1 change of parameter. The original boundary curve only needs
to be Lipschitz; Rademacher and the true null-set transport supply its
derivative at the composed points. -/
theorem herglotzConormal_traceReparam_ae {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    herglotzConormal k a (γ ∘ τ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        (fun θ => deriv τ θ • herglotzConormal k a γ (τ θ)) := by
  obtain ⟨D, hD⟩ := hτ.lipschitz
  filter_upwards [ae_restrict_of_ae (ae_deriv_comp hK hτ.monotone hD)] with θ hθ
  rw [herglotzConormal_eq ha.intervalIntegrable, hθ,
    herglotzConormal_eq ha.intervalIntegrable]
  simp only [Function.comp_apply, Complex.real_smul,
    map_mul, Complex.conj_ofReal]
  ring

/-- Actual variable-speed coordinate conormal, as an ordinary L2 class. -/
def localConformalHerglotzCoordinateLoad (F : ℂ → ℂ) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (memLp_herglotzConormal ha k hΓLip).toLp
    (herglotzConormal k a (physicalCircleTrace F))

theorem localConformalHerglotzCoordinateLoad_ae (F : ℂ → ℂ) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (localConformalHerglotzCoordinateLoad F hΓLip ha k : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        herglotzConormal k a (physicalCircleTrace F) :=
  (memLp_herglotzConormal ha k hΓLip).coeFn_toLp

section ConformalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hcoord

include hγ hτ in
/-- The genuine Herglotz H1 vector has its actual variable-speed circle
trace. A true smooth cutoff and the proved trace identity establish it. -/
theorem localConformalHerglotz_coordinate_trace_ae
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (coords.trace (herglotzWaveH1 coords.bounded ha k) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        (fun θ => herglotzWave k a (physicalCircleTrace F θ)) := by
  obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz coords.bounded coords.lipschitz hγ ha k
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae coords f,
    ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  rw [ht, hcoord, hfγ _ (hτ.mapsTo (Ioc_subset_Icc_self hθ))]
  simpa only [physicalCircleTrace, hcoord] using (herglotzWave_eq k a (γ (τ θ))).symm

variable (F)

/-- The constructed physical Jacobian load equals the actual conormal
on the genuine variable-speed conformal circle. No load equality is an
input to this theorem. -/
theorem localConformalHerglotz_traceReparamConormal_eq_coordinateLoad
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    traceReparamConormalL2 hτ (herglotzConormalL2 hγ ha k) =
      localConformalHerglotzCoordinateLoad F hΓLip ha k := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΓ : physicalCircleTrace F = γ ∘ τ := by
    aesop
  have hrep := isC1TraceReparam_ae_comp hτ (herglotzConormalL2_ae hγ ha k)
  have hc := herglotzConormal_traceReparam_ae hKγ hτ ha k
  rw [← hΓ] at hc
  apply Lp.ext
  filter_upwards [traceReparamConormalL2_ae hτ (herglotzConormalL2 hγ ha k), hrep, hc,
    localConformalHerglotzCoordinateLoad_ae F hΓLip ha k] with θ ht hr hc hg
  simp_all

/-- In particular the normalized weak load is exactly half smoothing of
the actual coordinate conormal's unitary Fourier coefficients. -/
theorem localConformalHerglotzBoundaryLoad_eq_coordinateLoad
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k) =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha k)) := by
  unfold localConformalBoundaryLoad
  rw [localConformalHerglotz_traceReparamConormal_eq_coordinateLoad F hγ hτ hcoord hΓLip ha k]

end ConformalCoordinates

/-! The following computation is on genuine coordinate integrals, with
ordinary measure. In particular it proves the zero Fourier row as well
as every nonzero row, for arbitrary integrable inputs. -/

private theorem regular_sawtooth_measurable :
    Measurable (Function.uncurry sawtoothKernel) := by
  unfold sawtoothKernel Function.uncurry
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_real_sign.comp (measurable_fst.sub measurable_snd)))).sub
    (measurable_const.mul
      (((Complex.measurable_ofReal.comp measurable_fst).sub
        (Complex.measurable_ofReal.comp measurable_snd)).div_const (π : ℂ)))

private theorem regular_sawtooth_norm_le {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    ‖sawtoothKernel θ s‖ ≤ 3 := by
  have hd : |θ - s| ≤ 2 * π := abs_le.mpr ⟨by grind,
    by grind⟩
  have hdiv : |(θ - s) / π| ≤ 2 := by
    rw [abs_div, abs_of_pos pi_pos]
    exact (div_le_iff₀ pi_pos).mpr (by linarith)
  calc
    ‖sawtoothKernel θ s‖ ≤
        ‖Complex.I * (Real.sign (θ - s) : ℂ)‖ +
          ‖Complex.I * (((θ - s) / π : ℝ) : ℂ)‖ := by
      simpa only [sawtoothKernel, Complex.ofReal_div, Complex.ofReal_sub] using
        (norm_sub_le (Complex.I * (Real.sign (θ - s) : ℂ))
          (Complex.I * (((θ - s) / π : ℝ) : ℂ)))
    _ = |Real.sign (θ - s)| + |(θ - s) / π| := by grind [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 3 := by linarith [abs_real_sign_le (θ - s)]

private theorem regular_sawtooth_swap (θ s : ℝ) :
    sawtoothKernel θ s = -sawtoothKernel s θ := by
  have hs : Real.sign (θ - s) = -Real.sign (s - θ) := by
    rw [← Real.sign_neg, neg_sub]
  simp only [sawtoothKernel, hs, Complex.ofReal_neg]
  ring

private theorem regular_kernel_mode_norm (n : ℤ) (θ : ℝ) :
    ‖kernelFourierMode n θ‖ = 1 := by
  rw [← fourier_two_pi_eq_kernelFourierMode]
  rw [fourier_apply]
  exact Circle.norm_coe _

private theorem regular_sawtooth_outer_mode (n : ℤ) {s : ℝ}
    (hs : s ∈ Icc 0 (2 * π)) :
    (∫ θ in (0 : ℝ)..(2 * π), kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      (2 / (n : ℂ)) * kernelFourierMode (-n) s := by
  have heq : (fun θ => kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      fun θ => -(sawtoothKernel s θ * kernelFourierMode (-n) θ) := by
    funext θ
    rw [regular_sawtooth_swap]
    ring
  rw [heq, intervalIntegral.integral_neg]
  by_cases hn : n = 0
  · subst n
    simp only [neg_zero, kernelFourierMode, Int.cast_zero, zero_mul,
      Complex.exp_zero, mul_one, div_zero, zero_mul]
    rw [integral_sawtoothKernel hs, neg_zero]
  · rw [show (∫ θ in (0 : ℝ)..(2 * π),
        sawtoothKernel s θ * kernelFourierMode (-n) θ) =
        2 / ((-n : ℤ) : ℂ) * kernelFourierMode (-n) s from
        integral_sawtoothKernel_mul_exp hs (neg_ne_zero.mpr hn)]
    grind

/-- The genuine sawtooth integral has multiplier `2/n` on every
Fourier coefficient of an arbitrary L1 input. At `n=0` the result is
exactly zero; the normalization remains `1/(2π)`. -/
theorem fourierCoeffOn_sawtoothAction {f : ℝ → ℂ}
    (hf : Integrable f (volume.restrict (Ioc 0 (2 * π)))) (n : ℤ) :
    fourierCoeffOn two_pi_pos
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) n =
        (2 / (n : ℂ)) * fourierCoeffOn two_pi_pos f n := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    exact (((show Continuous (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1) by
      unfold kernelFourierMode; fun_prop).measurable.aestronglyMeasurable.mul
      regular_sawtooth_measurable.aestronglyMeasurable).mul
      hf.aestronglyMeasurable.comp_snd)
  have hint : Integrable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    refine ((hf.norm.comp_snd μ).const_mul 3).mono' hm ?_
    have hae : ∀ᵐ p ∂μ.prod μ,
        p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
      dsimp [μ]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hae] with p hp
    simp only [norm_mul, regular_kernel_mode_norm, one_mul]
    exact mul_le_mul_of_nonneg_right
      (regular_sawtooth_norm_le (Ioc_subset_Icc_self hp.1)
        (Ioc_subset_Icc_self hp.2)) (norm_nonneg _)
  have hmode (θ : ℝ) :
      Complex.exp (2 * π * Complex.I * (-n : ℤ) * θ / ((2 * π : ℝ) : ℂ)) =
        kernelFourierMode (-n) θ := by
    simpa only [fourier_coe_apply] using fourier_two_pi_eq_kernelFourierMode (-n) θ
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  simp_rw [hmode]
  push_cast
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  change (1 / (2 * π) : ℂ) *
      (∫ θ, kernelFourierMode (-n) θ *
        (∫ s, sawtoothKernel θ s * f s ∂μ) ∂μ) = _
  have hsplit : (fun θ => kernelFourierMode (-n) θ *
      (∫ s, sawtoothKernel θ s * f s ∂μ)) =
      fun θ => ∫ s, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ := by
    funext θ
    rw [← integral_const_mul]
    ring
  rw [hsplit, integral_integral_swap hint]
  have heq : (fun s => ∫ θ,
      kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ) =ᵐ[μ]
      fun s => (2 / (n : ℂ)) * (kernelFourierMode (-n) s * f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [integral_mul_const]
    have hmode := regular_sawtooth_outer_mode n (Ioc_subset_Icc_self hs)
    rw [intervalIntegral.integral_of_le two_pi_pos.le] at hmode
    grind
  rw [integral_congr_ae heq, integral_const_mul]
  ring

/-- The genuine sawtooth action of any L1 input is L2 on the finite
parameter interval. This follows from its actual integral bound. -/
theorem memLp_sawtoothAction {f : ℝ → ℂ}
    (hf : Integrable f (volume.restrict (Ioc 0 (2 * π)))) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hmeas : AEStronglyMeasurable
      (fun θ => ∫ s, sawtoothKernel θ s * f s ∂μ) μ :=
    (regular_sawtooth_measurable.aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas (3 * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    ‖∫ s, sawtoothKernel θ s * f s ∂μ‖ ≤ ∫ s, 3 * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul 3)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (regular_sawtooth_norm_le (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The actual sawtooth boundary vector for an arbitrary L2 input. -/
def sawtoothBoundaryAction (f : BoundaryL2) : BoundaryL2 :=
  (memLp_sawtoothAction ((Lp.memLp f).integrable (by norm_num))).toLp _

theorem sawtoothBoundaryAction_fourier (f : BoundaryL2) (n : ℤ) :
    boundaryFourier (sawtoothBoundaryAction f) n =
      (2 / (n : ℂ)) * boundaryFourier f n := by
  rw [boundaryFourier_apply, boundaryFourier_apply]
  have hf := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hact : (sawtoothBoundaryAction f : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc 0 (2 * π))]
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) := by
    exact MemLp.coeFn_toLp (memLp_sawtoothAction hf)
  rw [fourierCoeffOn_congr_ae two_pi_pos hact]
  rw [fourierCoeffOn_sawtoothAction hf]
  ring

private theorem regular_half_weight_square (n : ℤ) :
    ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (sobWeight n : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num
  rw [Real.rpow_neg_one, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sobWeight_pos n).ne', Complex.ofReal_one]

/-- This actual bounded composition is the raw inverse derivative.
Its equality with the sawtooth integral is proved below, on all L2. -/
def regularRawInverseDerivative : L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2) (by norm_num)).comp
    ((principalNormalized - (2 : ℂ) • normalizedInverseAbsOperator).comp
      (sobolevSmoothing (1 / 2) (by norm_num)))

theorem regularRawInverseDerivative_apply (f : L2Z) (n : ℤ) :
    regularRawInverseDerivative f n = (2 / (n : ℂ)) * f n := by
  simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    principalNormalized, normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply]
  by_cases hn : n = 0
  simp_all [principalSymbol, normalizedInverseAbsSymbol]
  · have hsymbol : principalSymbol n - 2 * normalizedInverseAbsSymbol n =
        (sobWeight n : ℂ) * (2 / (n : ℂ)) := by
      simp only [principalSymbol, normalizedInverseAbsSymbol, if_neg hn]
      push_cast
      ring
    grind [regular_half_weight_square, one_mul]




/-- The bounded boundary operator obtained from the genuine raw Fourier
multiplier. It equals the original coordinate sawtooth integral on all L2. -/
def sawtoothBoundaryOperator : BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    (regularRawInverseDerivative.comp boundaryFourier.toLinearIsometry.toContinuousLinearMap)

theorem sawtoothBoundaryOperator_eq_action (f : BoundaryL2) :
    sawtoothBoundaryOperator f = sawtoothBoundaryAction f := by
  apply boundaryFourier.injective
  apply lp.ext
  funext n
  change boundaryFourier (boundaryFourier.symm
    (regularRawInverseDerivative (boundaryFourier f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, regularRawInverseDerivative_apply,
    sawtoothBoundaryAction_fourier]

/-- The corrected integral operator on ordinary boundary L2, transported
through the actual unitary circle lift. Both maps use their true measures. -/
def regularCorrectedBoundaryOperator {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryCircleUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((correctedKernelL2Op hK hW hc).comp
      boundaryCircleUnitary.toLinearIsometry.toContinuousLinearMap)

theorem regularCorrectedBoundaryOperator_fourier
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (f : BoundaryL2) :
    boundaryFourier (regularCorrectedBoundaryOperator hK hW hc f) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) := by
  change (fourierBasis (T := 2 * π)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hK hW hc (boundaryCircleUnitary f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    correctedKernelL2Op_fourier_action hK hW hc hr]
  rfl

/-- Raw square summability follows from the genuine normalized matrix
bound, without an arclength hypothesis on the conformal parameter. -/
theorem summable_regularKernelIntegralMatrix (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W p‖ ^ 2) :
    Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hbase
  have hm : 1 ≤ (sobWeight p.1) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_sobWeight p.1) (by norm_num)
  have hn : 1 ≤ (sobWeight p.2) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_sobWeight p.2) (by norm_num)
  have hweight := one_le_mul_of_one_le_of_one_le hm hn
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [correctedRemainderMatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  simpa using mul_le_mul_of_nonneg_right hweight (norm_nonneg (kernelIntegralMatrix p))

theorem memLp_regularCorrectedAction
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {f : ℝ → ℂ}
    (hf : Integrable f (volume.restrict (Ioc 0 (2 * π)))) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * f s) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hmeas : AEStronglyMeasurable
      (fun θ => ∫ s, correctedKernel W θ s * f s ∂μ) μ :=
    ((aestronglyMeasurable_correctedKernel hW).mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas ((4 + ‖cutBE W‖) * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    ‖∫ s, correctedKernel W θ s * f s ∂μ‖ ≤
        ∫ s, (4 + ‖cutBE W‖) * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul (4 + ‖cutBE W‖))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_correctedKernel_le hK hW (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

section ActualPeriodicOperator

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))

local notation "ΩP" => F '' ball (0 : ℂ) 1
local notation "QP" => localConformalDiskHalfTrace hR F hFs hL
local notation "TP" => localConformalDiskH1Trace hR F hFs hL

theorem localConformal_halfSmoothing_halfTrace (u : NeumannH1 ΩP) :
    sobolevSmoothing (1 / 2) (by norm_num) (QP u) = boundaryFourier (TP u) := by
  apply lp.ext
  funext n
  simpa only [fromL2, sobolevSmoothing, diagOp_apply, localConformalDiskHalfTrace,
    localConformalDiskH1Trace, ContinuousLinearMap.comp_apply] using
    congrFun (fromL2_half_diskHalfTrace (localConformalH1Pullback hR F hFs hL u)) n

end ActualPeriodicOperator

end PolyaNeumann

end
