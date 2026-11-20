/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.QuotientCap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The sharp bound and endpoint limit of the weighted circular normalizer -/

public section

open MeasureTheory Filter
open scoped Topology

namespace BergmanWeakType

open Weighted Real Set

private theorem tendsto_normalizer_boundary {α : ℝ} (hα : -1 < α) :
    Tendsto (normalizer (-(α + 2))) (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  unfold normalizer
  rw [show -(-(α + 2) + 2) = α by ring, ← circleAverage_boundary_power hα]
  by_cases hn : 0 ≤ α
  · exact ((continuous_const.sub continuous_id).norm.rpow_const (fun _ ↦ Or.inr hn)).circleAverage.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simp_rw [circleAverage_eq_integral_angleMeasure]
  let D := fun r θ : ℝ ↦ ‖1 - circleMap 0 r θ‖
  have hθ : ∀ᵐ θ ∂angleMeasure, 0 < D 1 θ := by
    filter_upwards [ae_mem_angle_open, angleMeasure.ae_ne 0] with θ hθ h0
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ h0 (eq_of_circleMap_eq (c := 0) one_ne_zero ?_ ?_))
    · rw [sub_zero, abs_lt]; grind [pi_pos]
    · simpa [circleMap] using h.symm

  have hi : Integrable (fun θ ↦ D 1 θ ^ α) angleMeasure := by
    apply Integrable.of_integral_ne_zero
    unfold D
    rw [← circleAverage_eq_integral_angleMeasure (f := fun z : ℂ ↦ ‖1 - z‖ ^ α),
      circleAverage_boundary_power hα]
    exact (gammaConstant_pos hα).ne'

  apply tendsto_integral_filter_of_dominated_convergence (fun θ ↦ (1 / 2 : ℝ) ^ α * D 1 θ ^ α)
  · exact .of_forall fun _ ↦ (show Measurable (fun θ ↦ D _ θ ^ α) by unfold D; fun_prop).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    filter_upwards [hθ] with θ ht
    have hsq (u : ℝ) : D u θ ^ 2 = polarDenominator 1 u θ := by
      simp [D, polarDenominator_eq_norm_sq]
    have hD : (1 / 2 : ℝ) * D 1 θ ≤ D r θ := by
      apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
      rw [mul_pow, hsq, hsq]
      simp [polarDenominator, radialComponent]
      nlinarith [sq_nonneg (1 - r), mul_nonneg (show 0 ≤ r - 1 / 4 by linarith [hr.1]) (sub_nonneg.mpr (cos_le_one θ))]
    simpa only [Real.norm_of_nonneg (rpow_nonneg (norm_nonneg _) _), mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.le] using
      rpow_le_rpow_of_nonpos (mul_pos (by norm_num) ht) hD (le_of_not_ge hn)
  · exact hi.const_mul _
  · filter_upwards [hθ] with θ ht
    exact ((show ContinuousAt (D · θ) 1 by unfold D; fun_prop).rpow_const (Or.inl ht.ne')).tendsto.mono_left nhdsWithin_le_nhds

/-- The sharp radial estimate used by the weak-type upper bound. -/
theorem radialMass_mul_normalizer_le {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r ≤ gammaConstant α := by
  rw [radialMass_mul_normalizer α ⟨hr, hr1⟩]
  apply ge_of_tendsto (tendsto_normalizer_boundary hα)
  filter_upwards [Ioo_mem_nhdsLT hr1] with R hR
  exact normalizer_mono _ hr hR.1.le hR.2

theorem tendsto_radialMass_mul_normalizer {α : ℝ} (hα : -1 < α) :
    Tendsto (fun r : ℝ ↦ (1 - r ^ 2) ^ (α + 1) * normalizer α r)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  apply (tendsto_normalizer_boundary hα).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  exact (radialMass_mul_normalizer α (Ioo_subset_Ico_self hr)).symm

end BergmanWeakType
