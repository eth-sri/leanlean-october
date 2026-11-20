/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorFiniteDifference
public import DOZZ.Hypergeom.Planar.RieszConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The real second derivative is dominated by the positive Riesz kernel. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The centered second difference of the parent kernel at the normalized center `1`. -/
noncomputable def planarRealSecondDifferenceQuotient (k β t : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) * normPowerRealSecondDifference k t (u - 1)

/-- Pointwise limit of the radial real second difference, multiplied by the singular weight. -/
noncomputable def planarRealSecondDifferenceLimit (k β : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) *
    ((k / 2) * (k / 2 - 1) * (‖u - 1‖ ^ 2) ^ (k / 2 - 2) *
        (2 * (u - 1).re) ^ 2 +
      (k / 2) * (‖u - 1‖ ^ 2) ^ (k / 2 - 1) * 2)

private theorem measurable_planarRealSecondDifferenceQuotient (k β t : ℝ) :
    Measurable (planarRealSecondDifferenceQuotient k β t) := by
  unfold planarRealSecondDifferenceQuotient normPowerRealSecondDifference radialSecondDiff
  fun_prop

/-- Dominated convergence when a quarter-plane difference quotient is bounded by the Riesz kernel. -/
theorem tendsto_integral_of_riesz_majorant (k β C : ℝ) (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)
    (F : ℝ → ℂ → ℝ) (G : ℂ → ℝ) (hF : ∀ t, Measurable (F t))
    (hb : ∀ t u, t ≠ 0 → u ≠ 1 → ‖F t u‖ ≤ C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))
    (hG : ∀ u, u ≠ 1 → Tendsto (F · u) (𝓝[≠] (0 : ℝ)) (𝓝 (G u))) :
    Tendsto (fun t => ∫ u, F t u) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ u, G u)) := by
  have hI := (positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)).const_mul C
  refine tendsto_integral_filter_of_dominated_convergence _
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) ?_ hI ((Measure.ae_ne volume 1).mono hG)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (Measure.ae_ne volume 1).mono (hb t · ht ·)

/-- Pointwise second derivative limit of the weighted radial kernel. -/
theorem planarRealSecondDifferenceQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
  exact tendsto_const_nhds.mul (norm_rpow_real_centered_difference_tendsto k (u - 1) (sub_ne_zero.mpr hu))

/-- Dominated convergence for the real second derivative of the normalized parent. -/
theorem planarRealSecondDifferenceQuotient_integral_tendsto (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ u : ℂ, planarRealSecondDifferenceLimit k β u)) := by
  refine tendsto_integral_of_riesz_majorant k β (radialCenteredConstant k) hk hβ hβ₂ _ _
    (measurable_planarRealSecondDifferenceQuotient k β) ?_ (planarRealSecondDifferenceQuotient_tendsto k β)
  intro t u ht hu
  have hw : 0 ≤ ‖u‖ ^ (-β) := by positivity
  rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (normPowerRealSecondDifference_le k hk (hβ.trans hβ₂)
    (u - 1) t (sub_ne_zero.mpr hu) ht) hw

end DOZZ.Proofs
