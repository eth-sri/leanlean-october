/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.Normalizer
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

variable {α : ℝ}

/-! # The sharp bound and endpoint limit of the weighted circular normalizer -/




open MeasureTheory Filter
open scoped Topology

namespace BergmanWeakType

theorem boundary_circleDenominator_pos {θ } (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    0 < circleDenominator 1 (Real.cos θ) := by
  have := lt_of_le_of_ne (Real.cos_le_one θ) (by
    rw [ne_eq, Real.cos_eq_one_iff_of_lt_of_lt (by grind) hθ.2]
    exact hθ.1.ne'
  )
  unfold circleDenominator
  nlinarith

theorem tendsto_circleAverage_boundaryPower (hα : -1 < α) :
    Tendsto (boundaryMoment α) (𝓝[<] 1) (𝓝 (gammaConstant α)) :=
  by
  by_cases hα0 : 0 ≤ α
  · have hc : Continuous (fun z : ℂ ↦ ‖1 - z‖ ^ α) :=
      (continuous_const.sub continuous_id).norm.rpow_const fun _ ↦ Or.inr hα0
    have hlim :=
      (Real.Continuous.circleAverage (c := 0) hc).continuousAt.tendsto |>.mono_left
        (show 𝓝[<] 1 ≤ 𝓝 1 from nhdsWithin_le_nhds)
    rw [circleAverage_boundary_power hα] at hlim
    exact hlim
  · have hα0 := lt_of_not_ge hα0
    let F := fun r θ ↦ circleDenominator r (Real.cos θ) ^ (α / 2)
    have hi : IntervalIntegrable (F 1) volume 0 (2 * Real.pi) :=
      by
      have h : CircleIntegrable (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 :=
        by
        by_contra hn
        have h := Real.circleAverage.integral_undef hn
        rw [circleAverage_boundary_power hα] at h
        exact (gammaConstant_pos hα).ne' h
      change IntervalIntegrable _ volume 0 _ at h
      simpa [F, ← norm_boundaryKernel_circleMap_rpow] using h
    have hlim :
      Tendsto (fun r ↦ ∫ θ in Set.Ioo 0 (2 * Real.pi), F r θ) (𝓝[<] 1) (𝓝 (∫ θ in Set.Ioo 0 (2 * Real.pi), F 1 θ)) :=
      by
      apply tendsto_integral_filter_of_dominated_convergence (fun θ ↦ (1 / 2) ^ (α / 2) * F 1 θ)
      · exact Filter.Eventually.of_forall fun r ↦ by
          apply Measurable.aestronglyMeasurable
          dsimp [F]
          fun_prop [circleDenominator]
      · filter_upwards [Ioo_mem_nhdsLT one_half_lt_one] with r hr
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ'
        have hd := boundary_circleDenominator_pos hθ'
        have he : 1 / 2 * circleDenominator 1 (Real.cos θ) ≤ circleDenominator r (Real.cos θ) := by
          simp_all [circleDenominator] <;> nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
        simpa only [Real.mul_rpow one_half_pos.le hd.le] using
          Real.rpow_le_rpow_of_nonpos (mul_pos one_half_pos hd) he (by linarith)
      · exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le Real.two_pi_pos.le).mp hi).const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ'
        have hc : ContinuousAt (fun r ↦ F r θ) 1 :=
          (show ContinuousAt (fun r ↦ circleDenominator r _) 1 by fun_prop [circleDenominator]).rpow_const
            (Or.inl (boundary_circleDenominator_pos hθ').ne')
        exact hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [← circleAverage_boundary_power hα]
    convert hlim.const_mul (2 * Real.pi)⁻¹ using 1
    all_goals
      try (ext r; rw [boundaryMoment, Real.circleAverage_eq_circleAverage_zero_one])
      simp [Real.circleAverage_def, ← norm_boundaryKernel_circleMap_rpow, F,
        intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo]



end BergmanWeakType
