/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Rigidity.KernelTransform
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import BergmanWeakType.WeightedSharp
import Mathlib.Tactic

variable {a b : ℂ} {K : ℂ → ℂ → ℂ}




open Set MeasureTheory Metric


namespace BergmanWeakType

theorem image_affine_disk  (hb : b ≠ 0) :
    (fun w ↦ a + b * w) '' disk = ball a ‖b‖ := by
  change (fun w ↦ a + b • w) '' ball 0 1 = _
  rw [← Set.image_image, Set.image_smul, smul_unitBall hb]
  simp

/-- Every Euclidean disk has positive Bergman weak type constant one. -/
theorem weakTypeConstant_domainPositiveProjection_ball_eq_one (a) {R} (hR : 0 < R) (hK : IsBergmanKernel (ball a R) K) :
    weakTypeConstant (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) = 1 :=
  by
  have hnorm : ‖(R : ℂ)‖ = R := by simp_all <;> nlinarith
  have : IsFiniteMeasure (area.restrict (ball a R)) := isFiniteMeasure_restrict.mpr isBounded_ball.measure_lt_top.ne
  apply le_antisymm
  · apply sInf_le
    rw [← hnorm] at hK ⊢
    let b : ℂ := R
    have hb : b ≠ 0 := (Complex.ofReal_ne_zero.mpr hR.ne')
    let e := (MeasurableEquiv.mulLeft₀ b hb).trans (MeasurableEquiv.addLeft a)
    have hbij : BijOn e disk (ball a ‖b‖) := by
      rw [← image_affine_disk hb]
      exact e.injective.injOn.bijOn_image
    let c := ENNReal.ofReal (‖b‖ ^ 2)
    have hμ := (map_withDensity_abs_det_fderiv_eq_addHaar area
      (s := disk) isOpen_ball.measurableSet.nullMeasurableSet
      (fun w _ ↦ (((hasDerivAt_const_mul b).const_add a).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      hbij.injOn).symm
    simp (disch := fun_prop) only [det_complex_derivative, abs_sq, withDensity_const,
      Measure.map_smul, image_affine_disk hb] at hμ
    change _ = c • Measure.map e diskArea at hμ
    intro f hf t ht
    have hfi := by
      rw [hμ] at hf
      exact e.measurableEmbedding.integrable_map_iff.mp ((integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb))) (ENNReal.ofReal_ne_top)).mp hf)
    rw [hμ, Measure.smul_apply, smul_eq_mul, e.map_apply, lintegral_smul_measure, e.measurableEmbedding.lintegral_map,
      one_mul]
    rw [smul_eq_mul, ← mul_assoc, mul_comm (ENNReal.ofReal t) c, mul_assoc]
    apply mul_le_mul_right _ c
    have hbound := isWeakTypeBound_weightedPositiveProjection neg_one_lt_zero
    simp [IsWeakTypeBound, weightedPositiveProjection] at hbound
    convert (hbound _ hfi t ht) using 1
    · congr 1
      apply measure_congr
      filter_upwards [ae_mem_disk] with z hz
      simp only [mem_preimage, mem_ofPred_eq]
      congr 1
      have hederiv (w) : deriv e w = b := ((hasDerivAt_const_mul b).const_add a).deriv
      have hcoef {w} (hw : w ∈ disk) :=
        by
        have hk := hK.disk_jacobian_formula isOpen_ball (by
          simp [e, MeasurableEquiv.coe_trans]
          fun_prop
        ) (by
          simp [e, MeasurableEquiv.coe_trans]
          fun_prop
        ) hbij (⟨fun _ _ ↦ e.symm_apply_apply _, fun _ _ ↦ e.apply_symm_apply _⟩) hz hw
        simp only [hederiv, mul_div_cancel_left₀ _ hb] at hk
        simpa only [norm_smul, Real.norm_eq_abs, abs_sq, ENNReal.ofReal_mul (sq_nonneg _)] using
          congrArg (fun z : ℂ ↦ ENNReal.ofReal ‖z‖) hk
      change ∫⁻ w, ENNReal.ofReal _ * ‖f w‖ₑ ∂area.restrict _ = _
      rw [hμ, lintegral_smul_measure, e.measurableEmbedding.lintegral_map, smul_eq_mul, ←
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_mem_disk] with w hw
      rw [← mul_assoc, hcoef hw]
      simp
    · continuity
  · let μ := area.restrict (ball a R)
    simpa only [enorm_one, lintegral_const, one_mul,
      ENNReal.div_self (by simpa [μ] using (measure_ball_pos area a hR).ne') (measure_ne_top μ Set.univ)] using
      measure_univ_div_mass_le_weakTypeConstant_of_witness
        (μ := μ) (T := domainPositiveProjection (ball a R) K) (integrable_const 1) (by
          filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
          have hnorm := enorm_integral_le_lintegral_enorm (μ := μ) (K z)
          rw [hK.integral_section_eq_one hz] at hnorm
          simpa [domainPositiveProjection, ← ofReal_norm] using hnorm
        )

end BergmanWeakType
