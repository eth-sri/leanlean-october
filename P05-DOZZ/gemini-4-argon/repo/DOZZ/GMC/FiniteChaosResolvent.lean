/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Prod

/-! Resolvent comparisons obtained by integrating the finite-chaos Laplace comparison. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The reciprocal of a positive scalar is the Laplace integral of its negative exponential. -/
theorem ofReal_inv_eq_lintegral_exp_neg_mul {u} (hu : 0 < u) :
    ENNReal.ofReal (u⁻¹) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(u * s))) ∂volume := by
  rw [← (ofReal_integral_eq_lintegral_ofReal (show IntegrableOn (fun s => Real.exp (-(u * s))) (Ioi (0 : ℝ)) volume by simpa using (integrableOn_Ioi_comp_mul_left_iff (fun s => Real.exp (-s)) 0 hu).2 (by simpa using (by simpa [Real.rpow_zero] using (Real.GammaIntegral_convergent (show 0 < (1 : ℝ) by norm_num))))) (by filter_upwards [] with s; exact (Real.exp_nonneg _))), (show (∫ s in Ioi (0 : ℝ), Real.exp (-(u * s)) ∂volume) = u⁻¹ by convert (integral_exp_neg_mul_rpow (p := 1) (b := u) zero_lt_one hu) using 1 <;> simp [Real.Gamma_add_one, Real.Gamma_one, Real.rpow_one, Real.rpow_neg_one])]


/-- A resolvent fraction is integrable on a probability space because its reciprocal part is
bounded by the positive scalar parameter. -/
theorem resolvent_fraction_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Ω → ℝ) (hm : AEMeasurable m P) (hm0 : ∀ ω, 0 ≤ m ω)
    t (ht : 0 < t) :
    Integrable (fun ω => m ω / (t + m ω)) P := by
  have heq : (fun ω => m ω / (t + m ω)) =
      fun ω => 1 - t * (t + m ω)⁻¹ := by
    funext ω
    field_simp [(ne_of_gt (by linarith [ht, hm0 ω]) : t + m ω ≠ 0)]
    ring
  rw [heq]
  exact (integrable_const (1 : ℝ)).sub (((integrable_const (t⁻¹)).mono' (show AEMeasurable (fun ω => (t + m ω)⁻¹) P by exact (show Measurable (fun x => (t + x)⁻¹) by fun_prop).comp_aemeasurable hm).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith [ht, hm0 ω]))]; simpa [one_div] using one_div_le_one_div_of_le ht (show t ≤ t + m ω by linarith [hm0 ω])))).const_mul t)

/-- The associated bounded fraction has the reverse expectation order. Its expectation is
`1 - t E[(t + m)⁻¹]`, and the probability-space means of the constant terms agree. -/
theorem laplace_order_fraction_expectation
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (m : Ω → ℝ) (m' : Ω' → ℝ)
    (hm : AEMeasurable m P) (hm' : AEMeasurable m' P')
    (hm0 : ∀ ω, 0 ≤ m ω) (hm'0 : ∀ ω, 0 ≤ m' ω)
    (hLap : ∀ s : ℝ, 0 ≤ s →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * m ω))) ∂P ≤
        ∫⁻ ω', ENNReal.ofReal (Real.exp (-(s * m' ω'))) ∂P')
    t (ht : 0 < t) :
    ∫ ω, m ω / (t + m ω) ∂P ≥ ∫ ω', m' ω' / (t + m' ω') ∂P' := by
  have laplace_order_resolvent : ∫⁻ ω, ENNReal.ofReal ((t + m ω)⁻¹) ∂P ≤ ∫⁻ ω', ENNReal.ofReal ((t + m' ω')⁻¹) ∂P' := by
    let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
    let f : Ω → ℝ → ℝ≥0∞ := fun ω s =>
      ENNReal.ofReal (Real.exp (-(s * (t + m ω))))
    let f' : Ω' → ℝ → ℝ≥0∞ := fun ω s =>
      ENNReal.ofReal (Real.exp (-(s * (t + m' ω))))
    rw [show (∫⁻ ω, ENNReal.ofReal ((t + m ω)⁻¹) ∂P) =
        ∫⁻ ω, ∫⁻ s, f ω s ∂ν ∂P by
          apply lintegral_congr_ae
          exact ae_of_all P (fun ω => by simpa [f, ν, mul_comm] using ofReal_inv_eq_lintegral_exp_neg_mul (u := t + m ω) (add_pos_of_pos_of_nonneg ht (hm0 ω)))]
    rw [show (∫⁻ ω', ENNReal.ofReal ((t + m' ω')⁻¹) ∂P') =
        ∫⁻ ω', ∫⁻ s, f' ω' s ∂ν ∂P' by
          apply lintegral_congr_ae
          exact ae_of_all P' (fun ω => by simpa [f', ν, mul_comm] using ofReal_inv_eq_lintegral_exp_neg_mul (u := t + m' ω) (add_pos_of_pos_of_nonneg ht (hm'0 ω)))]
    rw [lintegral_lintegral_swap (show AEMeasurable (Function.uncurry f) (P.prod ν) by exact ((show Measurable (fun z : ℝ × ℝ => Real.exp (-(z.1 * z.2))) by fun_prop).comp_aemeasurable (measurable_snd.aemeasurable.prodMk <| (continuous_const_add t).measurable.comp_aemeasurable hm.comp_fst)).ennreal_ofReal), lintegral_lintegral_swap (show AEMeasurable (Function.uncurry f') (P'.prod ν) by exact ((show Measurable (fun z : ℝ × ℝ => Real.exp (-(z.1 * z.2))) by fun_prop).comp_aemeasurable (measurable_snd.aemeasurable.prodMk <| (continuous_const_add t).measurable.comp_aemeasurable hm'.comp_fst)).ennreal_ofReal)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hfactor : (∫⁻ ω, f ω s ∂P) =
        ENNReal.ofReal (Real.exp (-(s * t))) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * m ω))) ∂P) := by
      rw [show (fun ω => f ω s) = fun ω =>
          ENNReal.ofReal (Real.exp (-(s * t))) *
            ENNReal.ofReal (Real.exp (-(s * m ω))) by
            funext ω
            dsimp [f]
            rw [show -(s * (t + m ω)) = -(s * t) + -(s * m ω) by ring,
              Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] ]
      exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
    have hfactor' : (∫⁻ ω', f' ω' s ∂P') =
        ENNReal.ofReal (Real.exp (-(s * t))) *
          (∫⁻ ω', ENNReal.ofReal (Real.exp (-(s * m' ω'))) ∂P') := by
      rw [show (fun ω' => f' ω' s) = fun ω' =>
          ENNReal.ofReal (Real.exp (-(s * t))) *
            ENNReal.ofReal (Real.exp (-(s * m' ω'))) by
            funext ω'
            dsimp [f']
            rw [show -(s * (t + m' ω')) = -(s * t) + -(s * m' ω') by ring,
              Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] ]
      exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
    rw [hfactor, hfactor']
    gcongr
    exact hLap s (le_of_lt hs)
  have hinvInt : Integrable (fun ω => (t + m ω)⁻¹) P :=
    (integrable_const (t⁻¹)).mono' (show AEMeasurable (fun ω => (t + m ω)⁻¹) P by exact (show Measurable (fun x => (t + x)⁻¹) by fun_prop).comp_aemeasurable hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith [ht, hm0 ω]))]; simpa [one_div] using one_div_le_one_div_of_le ht (show t ≤ t + m ω by linarith [hm0 ω])))
  have hinvInt' : Integrable (fun ω' => (t + m' ω')⁻¹) P' :=
    (integrable_const (t⁻¹)).mono' (show AEMeasurable (fun ω' => (t + m' ω')⁻¹) P' by exact (show Measurable (fun x => (t + x)⁻¹) by fun_prop).comp_aemeasurable hm').aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω' => by rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith [ht, hm'0 ω']))]; simpa [one_div] using one_div_le_one_div_of_le ht (show t ≤ t + m' ω' by linarith [hm'0 ω'])))
  have hInvNonneg' : ∀ ω', 0 ≤ (t + m' ω')⁻¹ := fun ω' =>
    inv_nonneg.mpr (by linarith [ht, hm'0 ω'])
  have hfracMean : (∫ ω, m ω / (t + m ω) ∂P) =
      1 - t * ∫ ω, (t + m ω)⁻¹ ∂P := by
    calc
      _ = ∫ ω, (1 - t * (t + m ω)⁻¹) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          field_simp [(ne_of_gt (by linarith [ht, hm0 ω]) : t + m ω ≠ 0)]
          ring
      _ = _ := by
        rw [integral_sub (integrable_const 1) (hinvInt.const_mul t), integral_const, integral_const_mul]
        simp
  have hfracMean' : (∫ ω', m' ω' / (t + m' ω') ∂P') =
      1 - t * ∫ ω', (t + m' ω')⁻¹ ∂P' := by
    calc
      _ = ∫ ω', (1 - t * (t + m' ω')⁻¹) ∂P' := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω' => by
          field_simp [(ne_of_gt (by linarith [ht, hm'0 ω']) : t + m' ω' ≠ 0)]
          ring
      _ = _ := by
        rw [integral_sub (integrable_const 1) (hinvInt'.const_mul t), integral_const, integral_const_mul]
        simp
  rw [hfracMean, hfracMean']
  nlinarith [mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae (Filter.Eventually.of_forall hInvNonneg'))).mp (by rw [(ofReal_integral_eq_lintegral_ofReal hinvInt (Filter.Eventually.of_forall (fun ω => inv_nonneg.mpr (by linarith [ht, hm0 ω])))), (ofReal_integral_eq_lintegral_ofReal hinvInt' (Filter.Eventually.of_forall hInvNonneg'))]; exact (laplace_order_resolvent))) ht.le]

end DOZZ.Proofs
