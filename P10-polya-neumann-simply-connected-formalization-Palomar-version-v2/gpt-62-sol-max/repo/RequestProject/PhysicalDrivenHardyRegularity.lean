module

public import RequestProject.CircleFourier
public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.FourierLipschitz
public import RequestProject.CutFourier
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Actual zeroth driven gauge with L² forcing

The exponential gauge gives the actual L² derivative of the zeroth row.
Fourier integration by parts and Parseval then give H¹ coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate



section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ)

include hK hγ hW in
private theorem physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGauge γ E (physicalDrivenVector W g) 0)
        (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) θ - Complex.I * g θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg] with θ hθ hi
  have h := hasDerivAt_physicalDrivenGauge_zero (a := 0) (hγ.differentiable_one θ)
    (by simpa only [zero_smul, add_zero] using hθ hi)
  refine h.congr_deriv ?_
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  rw [mul_zero, add_zero]
  field_simp [hs]
  ring

end

section

variable {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
  (hf' : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
  (hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt f (f' θ) θ)
  (hp : f 0 = f (2 * Real.pi))
include hf hf' hd hp

/-- Fourier integration by parts for an absolutely continuous function. -/
theorem fourierCoeffOn_of_ac_ae_hasDerivAt
     (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos f' n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos f n := by
  let e : ℝ → ℂ := fun θ => fourier (-n) (θ : AddCircle (2 * Real.pi))
  let α : ℂ := -(Complex.I * (n : ℂ))
  have hec : Continuous e := (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hen (θ : ℝ) : ‖e θ‖ = 1 := norm_fourier_coe (-n) θ
  have he1 : ContDiff ℝ 1 e := by
    dsimp only [e]
    simp_rw [fourier_coe_two_pi]
    have harg : ContDiff ℝ 1 (fun θ : ℝ => ((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const
    fun_prop
  have heD (θ : ℝ) : HasDerivAt e (α * e θ) θ := by
    have hα : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) /
        ((2 * Real.pi : ℝ) : ℂ) = α := by
      dsimp only [α]
      push_cast
      field_simp [Real.pi_ne_zero]
    simpa only [hα] using hasDerivAt_fourier_neg (2 * Real.pi) n θ
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := hfC.integrableOn_Icc
  have hf'i : IntegrableOn f' (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hf'
  have hfe : IntegrableOn (fun θ => f θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hfi.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hf'e : IntegrableOn (fun θ => f' θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hf'i.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hprodAC : AbsolutelyContinuousOnInterval (fun θ => f θ * e θ) 0 (2 * Real.pi) := by
    exact hf.smul (he1.absolutelyContinuousOnInterval)
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => f θ * e θ) (f' θ * e θ + α * (f θ * e θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    convert (hθ hmem).mul (heD θ) using 1; ring
  have hprodI : IntegrableOn (fun θ => f' θ * e θ + α * (f θ * e θ))
      (Icc 0 (2 * Real.pi)) := hf'e.add (hfe.const_mul α)
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hprodAC hprodI hprodD (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have he0 : e 0 = 1 := by
    change fourier (-n) ((0 : ℝ) : AddCircle (2 * Real.pi)) = 1
    simp
  have heL : e (2 * Real.pi) = 1 := by
    have hper : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      simp
    change fourier (-n) ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = 1
    rw [hper, fourier_eval_zero]
  have hi0 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      f' θ * e θ + α * (f θ * e θ)) = 0 := by
    rw [he0, heL, mul_one, mul_one, ← hp] at hFTC
    grind
  have hife : IntervalIntegrable (fun θ => f θ * e θ) volume 0 (2 * Real.pi) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hfe
  have hif'e : IntervalIntegrable (fun θ => f' θ * e θ) volume 0 (2 * Real.pi) := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf'e
  rw [intervalIntegral.integral_add hif'e (hife.const_mul α),
    intervalIntegral.integral_const_mul] at hi0
  have hi : (∫ θ in (0 : ℝ)..(2 * Real.pi), f' θ * e θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * e θ) := by
    dsimp only [α] at hi0
    grind
  have hi' : (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f' θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f θ) := by
    simpa only [mul_comm] using hi
  simp only [e, fourier_coe_apply] at hi'
  simp only [fourierCoeffOn_eq_integral, smul_eq_mul, Complex.real_smul,
    fourier_coe_apply, sub_zero]
  rw [hi']
  ring

/-- Actual AC and an L² a.e. derivative give the project's true Fourier
H¹ sequence, using Parseval for both value and derivative. -/
theorem isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
     :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos f) := by
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hs := (hasSum_sq_fourierCoeffOn Real.two_pi_pos
    (hfC.memLp_Ioc)).summable
  have hs' := (hasSum_sq_fourierCoeffOn Real.two_pi_pos hf').summable
  have hdn (n : ℤ) : ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ 2 =
      (n : ℝ) ^ 2 * ‖fourierCoeffOn Real.two_pi_pos f n‖ ^ 2 := by
    rw [fourierCoeffOn_of_ac_ae_hasDerivAt hf hf' hd hp n]
    grind [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow, sq_abs]
  change Summable (fun n : ℤ => (sobWeight n ^ (1 : ℝ) *
    ‖fourierCoeffOn Real.two_pi_pos f n‖) ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((hs.mul_left 2).add (hs'.mul_left 2))
  rw [hdn]
  simp  [sobWeight, Real.rpow_one]
  have h0 := norm_nonneg (fourierCoeffOn Real.two_pi_pos f n)
  have ha := abs_nonneg (n : ℝ)
  have hsq := sq_nonneg ((|(n : ℝ)| - 1) * ‖fourierCoeffOn Real.two_pi_pos f n‖)
  rw [← sq_abs (n : ℝ)]
  nlinarith

end

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) (hO : observationAdj W g = 0)
include γ K hK hγ E W hW g hg hO

/-- The actual zeroth gauge of an L² driven observation-kernel vector has
H¹ coefficients. No Sobolev premise on that vector is needed. -/
theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_one
     :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) := by
  have hgi := intervalIntegrable_boundary_of_memLp g hg
  have hends := physicalDrivenGauge_actual_endpoints γ E W g hO 0
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenGauge_absolutelyContinuous hγ
      (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hgi) E 0)
    ((physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hgi)).memLp_Ioc.sub
      (hg.const_smul Complex.I))
    (physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hgi)
    (hends.1.trans hends.2.symm)
  have hc (n : ℤ) : fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) n =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) n := by
    simp only [fourierCoeffOn_eq_integral, sub_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    dsimp 
    rw [physicalDrivenPeriodicGauge_eqOn γ E W g hO 0 hθ]
  exact hreg.congr fun n => by simp_all

theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_half
     :
    IsSobolevSeq (1 / 2 : ℝ)
      (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0)) :=
  (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hK hγ hW g hg hO)).1

end

end PolyaNeumann

end
