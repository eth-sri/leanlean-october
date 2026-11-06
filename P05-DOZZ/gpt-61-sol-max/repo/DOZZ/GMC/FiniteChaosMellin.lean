/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Mellin representation of negative powers by the Gamma integral. -/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- For a positive mass, its negative `q`th power is a normalized Laplace integral. -/
theorem ofReal_rpow_neg_eq_mellin_lintegral
    {m q : ℝ} (hm : 0 < m) (hq : 0 < q) :
    ENNReal.ofReal (m ^ (-q)) = ENNReal.ofReal (1 / Real.Gamma q) *
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m * t))) ∂volume := by
  have hI : IntegrableOn (fun t : ℝ => t ^ (q - 1) * Real.exp (-(m * t))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hq hm]
    positivity
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => t ^ (q - 1) * Real.exp (-(m * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hq hm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [one_div, Real.inv_rpow hm.le, Real.rpow_neg hm.le]
  field_simp [(Real.Gamma_pos_of_pos hq).ne', (Real.rpow_pos_of_pos hm q).ne']

/-- Mellin's formula in the extended nonnegative reals, also at zero. -/
theorem nonneg_rpow_neg_eq_mellin_lintegral
    {m q : ℝ} (hm : 0 ≤ m) (hq : 0 < q) :
    (ENNReal.ofReal m) ^ (-q) = ENNReal.ofReal (1 / Real.Gamma q) *
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m * t))) ∂volume := by
  rcases eq_or_lt_of_le hm with rfl | hm
  · simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hq),
      zero_mul, neg_zero, Real.exp_zero, mul_one]
    have htop : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) ∂volume = ∞ := by
      by_contra h
      apply not_integrableOn_Ioi_rpow (q - 1)
      refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal ?_).2 (lt_top_iff_ne_top.2 h)⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg ht.le _
    rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (one_div_pos.mpr (Real.Gamma_pos_of_pos hq))))]
  · rw [ENNReal.ofReal_rpow_of_pos hm]
    exact ofReal_rpow_neg_eq_mellin_lintegral hm hq


end DOZZ.Proofs
