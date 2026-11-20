/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.NormalizerRadial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The sharp bound and endpoint limit of the weighted circular normalizer -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BergmanWeakType
open Weighted

/-- A chord of the unit circle is at most twice as long as the chord ending at
any interior point on the same ray. This gives an integrable majorant for a
negative power, uniformly all the way to the boundary. -/
private theorem half_chord_le {r : ℝ} (hr : r ∈ Set.Ioo 0 1) {ζ : ℂ} (hz : ‖ζ‖ = 1) :
    ‖1 - ζ‖ / 2 ≤ ‖1 - (r : ℂ)*ζ‖ := by
  have h := dist_triangle 1 (r*ζ) ζ
  have h' := norm_sub_norm_le 1 (r*ζ)
  simp [dist_eq_norm, ← sub_one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, abs_of_pos hr.1, abs_of_neg (sub_neg.mpr hr.2)] at h h'
  simp at h h'; linarith

theorem tendsto_radialMoment {α : ℝ} (hα : -1 < α) :
    Tendsto (radialMoment α) (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  by_cases hα0 : 0 ≤ α
  · rw [← circleAverage_boundary_power hα]
    have hc : Continuous (radialMoment α) := by unfold radialMoment; fun_prop
    exact hc.continuousWithinAt
  · let F (r θ : ℝ) := ‖1 - r*circleMap 0 1 θ‖ ^ α
    let μ := volume.restrict (Set.Ioo 0 (2*Real.pi))
    have avg (r : ℝ) : radialMoment α r = (2*Real.pi)⁻¹ * ∫ θ, F r θ ∂μ := by
      simp [radialMoment,Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        integral_Ioc_eq_integral_Ioo,μ,F,circleMap]
    have endval := (avg 1).symm.trans (circleAverage_boundary_power hα)
    have hi : Integrable (F 1) μ := by
      grind [gammaConstant_pos, integral_undef]
    rw [funext avg, ← endval]
    apply Tendsto.const_mul
    apply tendsto_integral_filter_of_dominated_convergence (fun θ ↦ F 1 θ / 2^α)
      (.of_forall (by fun_prop)) _ (hi.div_const _) _
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
      filter_upwards [ae_restrict_mem  measurableSet_Ioo] with θ hθ
      have hp : 0 < ‖1 - circleMap 0 1 θ‖ := by
        grind [chord_length, Real.sin_pos_of_pos_of_lt_pi]
      simpa [F, Real.div_rpow hp.le zero_le_two, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
        Real.rpow_le_rpow_of_nonpos (half_pos hp) (by simp_all [half_chord_le]) (by grind)
    · filter_upwards [ae_restrict_mem  measurableSet_Ioo] with θ hθ
      apply ContinuousAt.tendsto  _ |>.mono_left nhdsWithin_le_nhds
      apply ContinuousAt.rpow_const (by fun_prop)
      simp [chord_length hθ, (Real.sin_pos_of_pos_of_lt_pi (by grind : 0 < θ/2) (by grind)).ne']

private theorem complementary (α r : ℝ) : normalizer (-α-2) r = radialMoment α r := by
  unfold normalizer; ring_nf

/-- The sharp radial estimate and its endpoint limit. -/
theorem radialMass_mul_normalizer_le {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    (1-r^2)^(α+1) * normalizer α r ≤ gammaConstant α := by
  rw [← driftWeight, radial_transform α ⟨hr,hr1⟩]
  apply ge_of_tendsto (tendsto_radialMoment hα)
  filter_upwards [Ioo_mem_nhdsLT hr1] with R hR
  rw [← complementary]; apply normalizer_mono <;> grind

theorem tendsto_radialMass_mul_normalizer {α : ℝ} (hα : -1 < α) :
    Tendsto (fun r : ℝ ↦ (1-r^2)^(α+1) * normalizer α r) (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  apply (tendsto_radialMoment hα).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [← complementary]; exact (radial_transform α ⟨hr.1.le,hr.2⟩).symm

end BergmanWeakType
