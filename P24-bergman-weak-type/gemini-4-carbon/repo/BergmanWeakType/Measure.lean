module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace BergmanWeakType

@[simp] theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by simp [disk]

theorem measurableSet_disk : MeasurableSet disk := isOpen_ball.measurableSet

instance area_isOpenPosMeasure : Measure.IsOpenPosMeasure area :=
  Measure.isOpenPosMeasure_smul volume (by positivity)

theorem norm_mul_star_lt_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : w ∈ disk) : ‖z * star w‖ < 1 := by
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans_lt ((mem_disk_iff w).mp hw)

theorem kernel_denominator_ne_zero_closed_left {ζ w : ℂ} (hζ : ‖ζ‖ ≤ 1) (hw : w ∈ disk) :
    1 - ζ * star w ≠ 0 := fun h ↦
  lt_irrefl _ ((sub_eq_zero.mp h).symm ▸ (norm_mul_star_lt_one hζ hw).trans_eq norm_one.symm)

theorem kernel_denominator_norm_lower (z : ℂ) {w : ℂ} (hw : w ∈ disk) :
    1 - ‖z‖ ≤ ‖1 - z * star w‖ := by
  have := mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le
  have := norm_sub_norm_le (1 : ℂ) (z * star w)
  simp only [norm_one, norm_mul, norm_star] at *; linarith

@[simp] theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

@[simp] theorem weightedKernel_zero (z w : ℂ) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg, ← inv_pow]

@[simp] theorem weightedArea_zero : weightedArea 0 = diskArea := by simp [weightedArea]

@[simp] theorem weightedProjection_zero (f : ℂ → ℂ) : weightedProjection 0 f = projection f := by
  funext z; simp [weightedProjection, projection]

@[simp] theorem weightedPositiveProjection_zero (f : ℂ → ℂ) :
    weightedPositiveProjection 0 f = positiveProjection f := by
  funext z; simp [weightedPositiveProjection, positiveProjection]

@[simp] theorem gammaConstant_zero : gammaConstant 0 = 1 := by simp [gammaConstant]

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α :=
  div_pos (Gamma_pos_of_pos (by linarith)) (sq_pos_of_pos (Gamma_pos_of_pos (by linarith)))

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk := ae_restrict_mem measurableSet_disk

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk :=
  (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

theorem hasDerivAt_radialWeight (p : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun x ↦ (1 - x ^ 2) ^ p) (-2 * p * u * (1 - u ^ 2) ^ (p - 1)) u := by
  convert ((hasDerivAt_pow 2 u).const_sub 1).rpow_const (p := p)
    (Or.inl (by nlinarith [hu.1, hu.2] : 1 - u ^ 2 ≠ 0)) using 1
  ring

theorem weightedArea_norm_gt {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖} = ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  have hp : 0 < α + 1 := by linarith
  let φ (u : ℝ) := (1 - u ^ 2) ^ (α + 1)
  have hφc : Continuous φ := (continuous_const.sub (continuous_pow 2)).rpow_const fun _ ↦ Or.inr hp.le
  have hφa : StrictAntiOn φ (Icc r 1) := fun u hu v hv huv ↦
    rpow_lt_rpow (by nlinarith [hv.1, hv.2]) (by nlinarith [hr, hu.1, hv.1]) hp
  have hSm : MeasurableSet {z : ℂ | r < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  let g : ℝ → ℝ≥0∞ := (Ioo r 1).indicator fun u ↦ ENNReal.ofReal (-(-2 * (α + 1) * u * (1 - u ^ 2) ^ (α + 1 - 1)))
  have hgm : Measurable g :=
    (((measurable_const.mul measurable_id).mul ((continuous_const.sub (continuous_pow 2)).measurable.pow_const _)).neg).ennreal_ofReal.indicator measurableSet_Ioo
  rw [weightedArea, withDensity_apply _ hSm, diskArea, Measure.restrict_restrict hSm,
    area, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_indicator (hSm.inter measurableSet_disk), ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet (g := fun p ↦ g p.1 * ENNReal.ofReal 2⁻¹)
      fun ⟨u, θ⟩ ⟨(hu : 0 < u), _⟩ ↦ by
        have hn : ‖Complex.polarCoord.symm (u, θ)‖ = u := by simp [abs_of_pos hu]
        have hm : Complex.polarCoord.symm (u, θ) ∈ {z : ℂ | r < ‖z‖} ∩ disk ↔ u ∈ Ioo r 1 := by
          simp [disk, abs_of_pos hu]
        by_cases h : u ∈ Ioo r 1
        · rw [smul_eq_mul, indicator_of_mem (hm.mpr h), hn, ← ENNReal.ofReal_mul hu.le]
          dsimp only [g]; rw [indicator_of_mem h, ← ENNReal.ofReal_mul' (by positivity), add_sub_cancel_right]
          congr 1; ring
        · rw [smul_eq_mul, indicator_of_notMem (mt hm.mp h)]; simp [g, h],
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hgm.aemeasurable aemeasurable_const, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioo,
    lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioi_self.trans' (Ioo_subset_Ioo_left hr)),
    ← ENNReal.ofReal_mul (by positivity), show 2⁻¹ * (π - -π) = π by ring,
    ← mul_assoc, mul_comm (ENNReal.ofReal π⁻¹), mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ pi_pos.ne', ENNReal.ofReal_one, mul_one,
    lintegral_deriv_eq_volume_image_of_antitoneOn measurableSet_Ioo
      (fun u hu ↦ (hasDerivAt_radialWeight (α + 1) ⟨hr.trans_lt hu.1, hu.2⟩).hasDerivWithinAt)
      (hφa.antitoneOn.mono Ioo_subset_Icc_self),
    hφc.continuousOn.image_Ioo_of_strictAntiOn hr1.le hφa, Real.volume_Ioo]
  simp [φ, zero_rpow hp.ne']

theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) :
    IsProbabilityMeasure (weightedArea α) :=
  ⟨by
    have hae : {z : ℂ | 0 < ‖z‖} =ᵐ[weightedArea α] univ :=
      ae_eq_univ.mpr <| (withDensity_absolutelyContinuous diskArea _).ae_le <| mem_ae_iff.mpr <|
        nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (by simp [area, norm_pos_iff]))
    simpa [← measure_congr hae] using weightedArea_norm_gt hα le_rfl zero_lt_one⟩

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea :=
  weightedArea_zero ▸ weightedArea_isProbabilityMeasure 0 (by norm_num)

theorem continuousOn_weightedKernel (α : ℝ) {z : ℂ} (hz : z ∈ disk) :
    ContinuousOn (weightedKernel α z) disk :=
  (continuous_const.sub (continuous_const.mul continuous_star)).continuousOn.cpow_const fun _ hw ↦
    Complex.mem_slitPlane_iff.mpr <| Or.inl <| by
      have hm := norm_mul_star_lt_one ((mem_disk_iff z).mp hz).le hw
      simpa only [Pi.sub_apply, Pi.mul_apply, Complex.sub_re, Complex.one_re] using
        sub_pos.mpr ((Complex.re_le_norm _).trans_lt hm)

theorem integrable_weightedKernel_mul {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun w ↦ weightedKernel α z w * f w) (weightedArea α) :=
  hf.bdd_mul (((continuousOn_weightedKernel α hz).aestronglyMeasurable
    (μ := area) measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _))
    ((ae_mem_disk_weightedArea α).mono fun _ hw ↦ by
      rw [norm_weightedKernel]
      exact rpow_le_rpow_of_nonpos (sub_pos.mpr ((mem_disk_iff z).mp hz))
        (kernel_denominator_norm_lower z hw) (by linarith))

theorem integral_diskArea_eq_circleAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r in Ioo (0 : ℝ) 1, (2 * r) • circleAverage f 0 r := by
  have hfi : Integrable (disk.indicator f) :=
    (integrable_indicator_iff measurableSet_disk).mpr <| by
      simp only [diskArea, area, Measure.restrict_smul] at hf
      exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mp hf
  have hsrc : IntegrableOn (disk.indicator f ∘ Complex.measurableEquivRealProd.symm)
      (polarCoord.symm '' polarCoord.target) := by
    rw [polarCoord.symm_image_target_eq_source]
    exact (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hfi).integrableOn
  have hp := ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn _).mp hsrc).congr
    (g := fun p : ℝ × ℝ ↦ p.1 • disk.indicator f (Complex.polarCoord.symm p))
    ((ae_restrict_mem polarCoord.open_target.measurableSet).mono fun p hp ↦ by
      simp only [det_fderivPolarCoordSymm, Function.comp_apply,
        Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
        abs_of_pos (show 0 < p.1 from hp.1)])
  rw [diskArea, area, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), ← integral_indicator measurableSet_disk,
    ← Complex.integral_comp_polarCoord_symm]
  change π⁻¹ • (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
    p.1 • disk.indicator f (Complex.polarCoord.symm p)) = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ hp, ← integral_smul,
    show Ioo (0 : ℝ) 1 = Ioi 0 ∩ Iio 1 by ext; simp, ← setIntegral_indicator measurableSet_Iio]
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr0 : 0 < r) ↦ ?_
  by_cases hr1 : r ∈ Iio 1
  · dsimp only
    rw [indicator_of_mem hr1, integral_smul r,
      setIntegral_congr_fun measurableSet_Ioo fun θ _ ↦ show
        disk.indicator f (Complex.polarCoord.symm (r, θ)) = f (Complex.polarCoord.symm (r, θ)) from
        indicator_of_mem (by simp [disk, abs_of_pos hr0, mem_Iio.mp hr1]) _,
      circleAverage_eq_integral_add (-π),
      intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap 0 r θ)) (-π), zero_add,
      show 2 * π + -π = π by ring, intervalIntegral.integral_of_le (by linarith [pi_pos]),
      integral_Ioc_eq_integral_Ioo,
      show (∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ))) =
        ∫ θ in Ioo (-π) π, f (circleMap 0 r θ) by
        congr 1; funext θ; simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I],
      smul_smul, smul_smul]
    congr 1; field_simp
  · rw [indicator_of_notMem hr1, integral_eq_zero_of_ae (.of_forall fun θ ↦ by
      dsimp; rw [indicator_of_notMem (by simpa [disk, abs_of_pos hr0] using hr1), smul_zero]), smul_zero]

theorem weightedDensity_toReal_ae {α : ℝ} (hα : -1 < α) :
    (fun z : ℂ ↦ (ENNReal.ofReal ((α + 1) * (1 - ‖z‖ ^ 2) ^ α)).toReal) =ᵐ[diskArea]
      fun z ↦ (α + 1) * (1 - ‖z‖ ^ 2) ^ α :=
  ae_mem_disk.mono fun z hz ↦ ENNReal.toReal_ofReal <| mul_nonneg (by linarith) <|
    rpow_nonneg (by nlinarith [(mem_disk_iff z).mp hz, norm_nonneg z]) _

theorem integral_weightedArea_eq_diskArea {α : ℝ} (hα : -1 < α) (f : ℂ → ℝ) :
    ∫ z, f z ∂weightedArea α = ∫ z, (α + 1) * (1 - ‖z‖ ^ 2) ^ α * f z ∂diskArea := by
  rw [weightedArea, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  exact integral_congr_ae <| (weightedDensity_toReal_ae hα).mono fun _ hz ↦ by simp [hz]

theorem integral_weightedArea_eq_circleAverage {α : ℝ} (hα : -1 < α)
    {f : ℂ → ℝ} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α = ∫ r in Ioo 0 1,
      (2 * r * ((α + 1) * (1 - r ^ 2) ^ α)) * circleAverage f 0 r := by
  have hi : Integrable (fun z ↦ (α + 1) * (1 - ‖z‖ ^ 2) ^ α * f z) diskArea :=
    ((integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hf).congr <|
      (weightedDensity_toReal_ae hα).mono fun _ hz ↦ by simp [hz]
  rw [integral_weightedArea_eq_diskArea hα, integral_diskArea_eq_circleAverage hi]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
  rw [smul_eq_mul, mul_assoc (2 * r)]; congr 1; rw [← smul_eq_mul, ← circleAverage_fun_smul]
  exact circleAverage_congr_sphere fun z hz ↦ by
    simp [show ‖z‖ = r by simpa [abs_of_pos hr.1] using hz]

theorem two_rpow_mul_integral_sin_rpow {α : ℝ} (hα : -1 < α) :
    (2 : ℝ) ^ α * (∫ x in 0..π, sin x ^ α) = π * gammaConstant α := by
  let p := (α - 1) / 2
  have hbeta : (∫ t in 0..1, t ^ p * (1 - t) ^ p) =
      Gamma ((α + 1) / 2) ^ 2 / Gamma (α + 1) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal, show _ =
        Complex.betaIntegral (Complex.ofReal ((α + 1) / 2)) (Complex.ofReal ((α + 1) / 2)) from
      intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht ↦ by
        simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
          Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le), Complex.ofReal_sub, Complex.ofReal_one]
        congr 2 <;> (dsimp [p]; push_cast; ring),
      Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) (by simp; linarith),
      ← Complex.ofReal_add, show (α + 1) / 2 + (α + 1) / 2 = α + 1 by ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← sq,
      ← Complex.ofReal_pow, ← Complex.ofReal_div]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := π) (f := fun x ↦ (1 - cos x) / 2) (f' := fun x ↦ sin x / 2)
    (g := fun t ↦ t ^ p * (1 - t) ^ p) (by fun_prop)
    (fun x _ ↦ by convert ((hasDerivAt_cos x).const_sub 1).div_const 2 using 1; ring)
    fun x hx ↦ by
      rw [min_eq_left pi_pos.le, max_eq_right pi_pos.le] at hx
      exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le) zero_le_two
  simp only [cos_zero, sub_self, zero_div, cos_pi, sub_neg_eq_add,
    show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Function.comp_def, hbeta] at hsub
  replace hsub : ((2 : ℝ) ^ α)⁻¹ * (∫ x in 0..π, sin x ^ α) =
      Gamma ((α + 1) / 2) ^ 2 / Gamma (α + 1) := by
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.integral_congr_Ioo_of_le pi_pos.le fun x hx ↦ ?_).symm
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hprod : ((1 - cos x) / 2) * (1 - (1 - cos x) / 2) = (sin x / 2) ^ 2 := by
      linear_combination -(sin_sq_add_cos_sq x) / 4
    rw [← mul_rpow (by linarith [cos_le_one x]) (by linarith [neg_one_le_cos x]), hprod,
      ← rpow_natCast (sin x / 2) 2, ← rpow_mul (by positivity), ← rpow_add_one (by positivity),
      show ((2 : ℕ) : ℝ) * p + 1 = α by dsimp [p]; ring,
      div_eq_inv_mul, mul_rpow (by norm_num) hs.le, inv_rpow zero_le_two]
  have htwo : (2 : ℝ) ^ α ≠ 0 := (rpow_pos_of_pos zero_lt_two α).ne'
  have hG1 : Gamma (α + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have hG2 : Gamma (1 + α / 2) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have hG := Gamma_mul_Gamma_add_half ((α + 1) / 2)
  rw [show (α + 1) / 2 + 1 / 2 = 1 + α / 2 by ring,
    show 2 * ((α + 1) / 2) = α + 1 by ring,
    show 1 - (α + 1) = -α by ring, rpow_neg zero_le_two] at hG
  have hG' : (2 : ℝ) ^ α * Gamma ((α + 1) / 2) * Gamma (1 + α / 2) = Gamma (α + 1) * sqrt π := by
    rw [mul_assoc, hG]; field_simp [htwo]
  have hsq := congrArg (· ^ 2) hG'
  rw [mul_pow, mul_pow, mul_pow, sq_sqrt pi_pos.le] at hsq
  have hI := congrArg (fun u ↦ (2 : ℝ) ^ α * ((2 : ℝ) ^ α * u)) hsub
  rw [mul_inv_cancel_left₀ htwo, ← mul_assoc] at hI
  rw [hI, gammaConstant, mul_div_assoc', mul_div_assoc',
    div_eq_div_iff hG1 (pow_ne_zero 2 hG2)]
  linear_combination hsq

end BergmanWeakType
