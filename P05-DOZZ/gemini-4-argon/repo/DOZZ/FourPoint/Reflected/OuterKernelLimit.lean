/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.OuterKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-! # Dominated removal of the moving exterior cutoff -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The literal real half-charge density is measurable, including all prescribed root values. -/
theorem reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z :
    Measurable (fun x => gammaHalfKernel γ α₁ α₂ α₃ z x) := by
  unfold gammaHalfKernel normPlus
  fun_prop

/-- The moving exterior integral converges whenever its zero-kernel mass is finite. -/
theorem reflected_outer_kernel_integral_tendsto (γ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (hξ : 0 < ξ) (hξ₁ : ξ < 1) (h0 : μ {0} = 0)
    (hfin : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ) ≠ ⊤) :
    Tendsto (fun z : ℂ => ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ)) := by
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  let F : ℂ → ℂ → ℝ≥0∞ := fun z =>
    {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}.indicator
      (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x))
  let C := ENNReal.ofReal ((2 : ℝ) ^ (γ ^ 2 / 2))
  let G : ℂ → ℝ≥0∞ := fun x => C * ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x)
  have hnorm : Tendsto (fun z => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ z in l, ∀ᵐ x ∂μ, F z x ≤ G x := by
    filter_upwards [(hnorm.eventually (gt_mem_nhds zero_lt_one)), self_mem_nhdsWithin] with z hz hz0
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : ‖z‖ ^ (1 - ξ) ≤ ‖x‖
    · have hr : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) := by
        simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hz0) hz.le (by linarith only [hξ] : 1 - ξ ≤ 1))
      dsimp only [F, G, C]
      rw [Set.indicator_of_mem (show x ∈ {u : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖u‖} from hx), ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
      exact ENNReal.ofReal_le_ofReal (reflected_outer_kernel_bound γ α₁ α₂ α₃ z x (hr.trans hx))
    · dsimp only [F]
      rw [Set.indicator_of_notMem (show x ∉ {u : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖u‖} from hx)]
      exact bot_le
  have hradius : Tendsto (fun z => ‖z‖ ^ (1 - ξ)) l (nhds 0) := by
    have he := sub_pos.mpr hξ₁
    simpa only [Function.comp_def, Real.zero_rpow he.ne'] using ((Real.continuous_rpow_const he.le).tendsto (0 : ℝ)).comp hnorm
  have hlimit : ∀ᵐ x ∂μ, Tendsto (fun z => F z x) l
      (nhds (ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x))) := by
    filter_upwards [(show ∀ᵐ x ∂μ, x ≠ 0 by rw [ae_iff]; simpa only [not_not, Set.ofPred_eq_eq_singleton] using h0)] with x hx
    apply (show Tendsto (fun z => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)) l (nhds (ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x))) by simpa only [Function.comp_def] using ((ENNReal.continuous_ofReal.comp (reflected_outer_kernel_continuous γ α₁ α₂ α₃ x)).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [(hradius.eventually (gt_mem_nhds (norm_pos_iff.mpr hx)))] with z hz
    dsimp only [F]
    rw [Set.indicator_of_mem (show x ∈ {u : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖u‖} from hz.le)]
  have hident z : (∫⁻ x, F z x ∂μ) =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := lintegral_indicator (isClosed_le continuous_const continuous_norm).measurableSet _
  simpa only [hident] using (tendsto_lintegral_filter_of_dominated_convergence G (Filter.Eventually.of_forall (show ∀ z, Measurable (F z) by intro z; exact (ENNReal.measurable_ofReal.comp (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z)).indicator (isClosed_le continuous_const continuous_norm).measurableSet)) hbound (by dsimp only [G]; rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlimit)

end DOZZ.Proofs
