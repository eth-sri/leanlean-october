/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceMarginal
public import DOZZ.Brownian.ConditionedEntranceProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Escape of deterministic entrance states

The explicit entrance density and its drift ordering show that the state tends to infinity in
probability. This is the one-time estimate used with the deterministic-time avoidance factor to
control late visits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Topology

namespace DOZZ.Proofs



/-- The conditioned path's positive coordinate escapes every fixed lower interval in real
measure at large deterministic times. -/
theorem conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) c (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 => P.real {p | -(p t) ≤ c})
      atTop (𝓝 0) := by
  have conditionedPositiveEntranceMeasure_cdf_tendsto_zero_atTop : Tendsto (fun t : ℝ => ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c) atTop (𝓝 0) := by
    have conditionedPositiveZeroDriftCDF_le_power {t} {c} (ht : 0 < t) (hc : 0 < c) : ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure 0 t) c ≤ Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := by
      let f := conditionedPositiveEntranceDensity 0 t
      let S := Set.Ioc 0 c
      let K := Real.sqrt (2 / Real.pi) * c ^ 2 / t ^ (3 / 2 : ℝ)
      let g := S.indicator (fun _ => K)
      have hfg : ∀ y ∈ Set.Iic c, f y ≤ g y := by
        intro y hy
        by_cases hy0 : y ≤ 0
        · have hfy : f y = 0 := by
            simp [f, conditionedPositiveEntranceDensity, hy0]
          rw [hfy, (show g y = 0 by simp [g, S, Set.indicator_of_notMem, hy0])]
        · have hypos : 0 < y := lt_of_not_ge hy0
          have hyS : y ∈ S := ⟨hypos, hy⟩
          have hexp : Real.exp (-y ^ 2 / (2 * t)) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            apply div_nonpos_of_nonpos_of_nonneg
            · exact neg_nonpos.mpr (sq_nonneg y)
            · positivity
          have hsqrt : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
          have hnum : Real.sqrt (2 / Real.pi) * y ^ 2 * Real.exp (-y ^ 2 / (2 * t)) ≤
              Real.sqrt (2 / Real.pi) * c ^ 2 := by
            calc
              _ ≤ Real.sqrt (2 / Real.pi) * c ^ 2 * Real.exp (-y ^ 2 / (2 * t)) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (by nlinarith [(mul_nonneg (sub_nonneg.mpr hy) (add_nonneg (le_of_lt hc) (le_of_lt hypos)))]) hsqrt) (Real.exp_nonneg _)
              _ ≤ Real.sqrt (2 / Real.pi) * c ^ 2 := by
                calc
                  _ ≤ (Real.sqrt (2 / Real.pi) * c ^ 2) * 1 :=
                    mul_le_mul_of_nonneg_left hexp (mul_nonneg hsqrt (sq_nonneg c))
                  _ = _ := mul_one _
          have hbound : f y ≤ K := by
            rw [(show f y = Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) * Real.exp (-y ^ 2 / (2 * t)) by simp [f, conditionedPositiveEntranceDensity, ht, hypos])]
            dsimp [K]
            calc
              Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) *
                  Real.exp (-y ^ 2 / (2 * t)) =
                  (Real.sqrt (2 / Real.pi) * y ^ 2 *
                    Real.exp (-y ^ 2 / (2 * t))) * (t ^ (3 / 2 : ℝ))⁻¹ := by ring
              _ ≤ (Real.sqrt (2 / Real.pi) * c ^ 2) *
                  (t ^ (3 / 2 : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (show 0 < t ^ (3 / 2 : ℝ) by positivity).le)
              _ = Real.sqrt (2 / Real.pi) * c ^ 2 / t ^ (3 / 2 : ℝ) := by ring
          simpa [g, Set.indicator_of_mem hyS] using hbound
      have hupper : (∫ y in Set.Iic c, g y) = K * c := by
        change (∫ y in Set.Iic c, S.indicator (fun _ => K) y) = K * c
        rw [setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr (by intro y hy; exact hy.2), setIntegral_const, smul_eq_mul]
        change (volume.real (Set.Ioc 0 c)) * K = K * c
        rw [Real.volume_real_Ioc_of_le hc.le]
        ring
      rw [conditionedPositiveEntranceMeasure_cdf_eq_integral (by norm_num) ht]
      calc
        (∫ y in Set.Iic c, f y) ≤ ∫ y in Set.Iic c, g y := (setIntegral_mono_on (integrable_conditionedPositiveEntranceDensity (by norm_num) ht).integrableOn ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (measure_Ioc_lt_top.ne))).integrableOn measurableSet_Iic hfg)
        _ = K * c := hupper
        _ = Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := by
          dsimp [K]
          ring
    have hνbound : ∀ᶠ t : ℝ in atTop,
        0 ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c ∧
        ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c ≤
          Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      constructor
      · exact ProbabilityTheory.cdf_nonneg _ _
      · calc
          _ ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure 0 t) c := (by rw [conditionedPositiveEntranceMeasure_cdf_eq_integral (ν := ν) (t := t) (z := c) hν.le ht, conditionedPositiveEntranceMeasure_cdf_eq_integral (ν := 0) (t := t) (z := c) (by norm_num) ht]; exact (conditionedPositiveEntranceDensity_drift_cdf_le (ν := 0) (ν' := ν) (by norm_num) hν.le ht c))
          _ ≤ Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := (conditionedPositiveZeroDriftCDF_le_power ht hc)
          _ = Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt ht)]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      (by simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 / 2 : ℝ))).const_mul (Real.sqrt (2 / Real.pi) * c ^ 3))
      (Filter.Eventually.of_forall fun t =>
        ProbabilityTheory.cdf_nonneg (conditionedPositiveEntranceMeasure ν t) c)
      (hνbound.mono fun _ h => h.2)
  apply ((conditionedPositiveEntranceMeasure_cdf_tendsto_zero_atTop).comp (NNReal.tendsto_coe_atTop.mpr (tendsto_id : Tendsto (fun t : ℝ≥0 => t) atTop atTop))).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  exact (conditionedPositiveStateAt_measureReal_Iic hP t (by exact_mod_cast ht) c).symm

end DOZZ.Proofs

end
