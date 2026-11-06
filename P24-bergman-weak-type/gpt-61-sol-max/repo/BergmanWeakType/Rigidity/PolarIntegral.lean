/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Definitions
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Module
import Mathlib.Tactic

/-! # Integration on the disk in polar coordinates -/




open Set MeasureTheory Metric Real


namespace BergmanWeakType

variable {q : ℝ} {E : Type*} [RCLike E]

/-- Integrable functions remain integrable after polar substitution with the Jacobian. -/
theorem integrable_polar {f : ℂ → E} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))
      polarCoord.target := by
  have hsource := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf).integrableOn (s := polarCoord.source)
  rw [← polarCoord.symm_image_target_eq_source] at hsource
  apply ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn _).mp hsource).congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  simp only [det_fderivPolarCoordSymm, Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
    abs_of_pos (show 0 < p.1 from hp.1)]

/-- Disk integration is twice the radius-weighted integral of circular means. -/
theorem integral_diskArea_eq_circleAverage {f : ℂ → E} (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r in unitIoo, (2 * r) • Real.circleAverage f 0 r :=
  by
  have hD : MeasurableSet disk := isOpen_ball.measurableSet
  have hp := integrable_polar ((integrable_indicator_iff hD).mpr ((integrable_smul_measure (c := ENNReal.ofReal Real.pi⁻¹) (by positivity) ENNReal.ofReal_ne_top).mp (by simpa [diskArea, area] using hf)))
  rw [diskArea, area, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le), ← integral_indicator hD, ←
    Complex.integral_comp_polarCoord_symm]
  change π⁻¹ • ∫ p in Ioi 0 ×ˢ Ioo (-π) π, p.1 • disk.indicator f (Complex.polarCoord.symm p) = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ hp, ← integral_smul]
  have hset : Ioi (0 : ℝ) ∩ Iio 1 = unitIoo := rfl
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  by_cases hr1 : r < 1
  · simp [Set.indicator, disk, abs_of_pos hr, hr1, integral_smul]
    rw [Real.circleAverage_eq_integral_add _,
      intervalIntegral.integral_comp_add_right (fun θ ↦ f _) _, zero_add,
      show 2 * π + -π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
    simp [smul_smul]
    congr 1
    · field
    · congr 1
      simp [circleMap, Complex.exp_mul_I]
  · simp [Set.indicator, hr1, disk, abs_of_pos hr]

theorem integral_unit_interval_rpow (hq : 0 < q) (F : ℝ → E) :
    ∫ y in unitIoo, F y = ∫ x in unitIoo, (q * x ^ (q - 1)) • F (x ^ q) :=
  by
  have him := by
    simpa [zero_rpow hq.ne'] using
      (continuous_rpow_const hq.le).continuousOn.image_Ioo_of_strictMonoOn
        zero_le_one
        ((strictMonoOn_rpow_Ici_of_exponent_pos hq).mono (fun x hx ↦ hx.1))
  unfold unitIoo
  nth_rw 1 [← him]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x hx ↦ (hasDerivAt_rpow_const  (Or.inl hx.1.ne')).hasDerivWithinAt) ((strictMonoOn_rpow_Ici_of_exponent_pos hq).injOn.mono (show unitIoo ⊆ Ici 0 from fun x hx ↦ hx.1.le))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [abs_of_pos (mul_pos hq (rpow_pos_of_pos hx.1 _))]

/-- Squared radius is the uniform radial coordinate for normalized disk area. -/
theorem integral_diskArea_eq_circleAverage_sqrt {f : ℂ → E} (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ y in unitIoo, Real.circleAverage f 0 (Real.sqrt y) :=
  by
  rw [integral_diskArea_eq_circleAverage hf,
    integral_unit_interval_rpow  zero_lt_two (fun y ↦ Real.circleAverage f 0 _)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  simp [show (2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_sq hr.1.le]

/-- The complementary squared radius is also uniform. -/
theorem integral_diskArea_eq_circleAverage_sqrt_one_sub {f : ℂ → E}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea =
      ∫ y in 0..1, Real.circleAverage f 0 (Real.sqrt (1 - y)) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun y ↦ Real.circleAverage f 0 _) 1]
  simp
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  exact?

end BergmanWeakType
