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

/-- Centered real second difference of the radial power. -/
noncomputable def normPowerRealSecondDifference (k t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2

/-- The centered second difference of the parent kernel at the normalized center `1`. -/
noncomputable def planarRealSecondDifferenceQuotient (k β t : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) * normPowerRealSecondDifference k t (u - 1)

/-- Pointwise limit of the radial real second difference, multiplied by the singular weight. -/
noncomputable def planarRealSecondDifferenceLimit (k β : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) *
    ((k / 2) * (k / 2 - 1) * (‖u - 1‖ ^ 2) ^ (k / 2 - 2) *
        (2 * (u - 1).re) ^ 2 +
      (k / 2) * (‖u - 1‖ ^ 2) ^ (k / 2 - 1) * 2)

private theorem measurable_nonneg_rpow {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (p : ℝ) : Measurable (fun u => f u ^ p) := by
  have hrepr : (fun u => f u ^ p) =
      fun u => if f u = 0 then 0 ^ p else Real.exp (p * Real.log (f u)) := by
    funext u
    by_cases hu : f u = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (hfn u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) hf
  · exact measurable_const
  · fun_prop

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg u) p






/-- Dominated convergence for the real second derivative of the normalized parent. -/
theorem planarRealSecondDifferenceQuotient_integral_tendsto k β
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ u : ℂ, planarRealSecondDifferenceLimit k β u)) := by
  have normPowerRealSecondDifference_le (hk₂ : k < 2) x t (hx : x ≠ 0) (ht : t ≠ 0) : |normPowerRealSecondDifference k t x| ≤ (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
    let C : ℝ := k * (1 + (15 / 4) *
      ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
    let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    change |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k -
      2 * ‖x‖ ^ k) / t ^ 2| ≤ _
    rw [abs_div, abs_of_pos ht2]
    calc
      _ ≤ ((2 * C + B) * ‖(t : ℂ)‖ ^ 2 * ‖x‖ ^ (k - 2)) / t ^ 2 :=
        div_le_div_of_nonneg_right (by simpa [C, B] using (norm_rpow_centered_difference_le_global k hk hk₂ x (t : ℂ) hx)) (le_of_lt ht2)
      _ = (2 * C + B) * ‖x‖ ^ (k - 2) := by
        rw [(show ‖(t : ℂ)‖ ^ 2 = t ^ 2 by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])]
        calc
          _ = (2 * C + B) * ‖x‖ ^ (k - 2) * (t ^ 2 / t ^ 2) := by ring
          _ = _ := by rw [div_self ht2.ne']; ring
      _ = (2 * (k * (1 + (15 / 4) *
          ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) +
          (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
            dsimp [C, B]
            ring
  have planarRealSecondDifferenceQuotient_tendsto u (hu : u ≠ 1) : Tendsto (fun t => planarRealSecondDifferenceQuotient k β t u) (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
    let w := ‖u‖ ^ (-β)
    have hrad := norm_rpow_real_centered_difference_tendsto k (u - 1) (sub_ne_zero.mpr hu)
    simpa [w, planarRealSecondDifferenceQuotient, planarRealSecondDifferenceLimit,
      normPowerRealSecondDifference, mul_assoc] using (tendsto_const_nhds.mul hrad)
  have integrable_planarRealSecondDifferenceQuotient t : Integrable (planarRealSecondDifferenceQuotient k β t) volume := by
    by_cases ht : t = 0
    · subst t
      rw [(show planarRealSecondDifferenceQuotient k β 0 = fun _ : ℂ => (0 : ℝ) by funext u; simp [planarRealSecondDifferenceQuotient, normPowerRealSecondDifference])]
      exact integrable_zero ℂ ℝ volume
    · let C : ℝ := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
          (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
      let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
      have hpoint : ∀ᵐ u ∂volume,
          ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
        filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
        have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
        rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg hnorm]
        exact (mul_le_mul_of_nonneg_left (normPowerRealSecondDifference_le (by linarith [hβ, hβ₂]) (u - 1) t (sub_ne_zero.mpr hu) ht) hnorm).trans_eq (by dsimp only [bound, C]; ring)
      apply (show Integrable bound volume by simpa [bound, C, mul_assoc] using (positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)).const_mul C).mono'
        ((show Measurable (planarRealSecondDifferenceQuotient k β t) by unfold planarRealSecondDifferenceQuotient; exact (measurable_complex_norm_rpow (-β)).mul ((by unfold normPowerRealSecondDifference; fun_prop)))).aestronglyMeasurable
      exact hpoint
  let C := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
    rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hnorm]
    exact (mul_le_mul_of_nonneg_left (normPowerRealSecondDifference_le (by linarith [hβ, hβ₂]) (u - 1) t (sub_ne_zero.mpr hu) (by simpa using ht)) hnorm).trans_eq (by dsimp only [bound, C]; ring)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (by filter_upwards [] with t; exact (integrable_planarRealSecondDifferenceQuotient t).aestronglyMeasurable) hbound (by simpa [bound, C, mul_assoc] using (positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)).const_mul C) (by filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu; exact planarRealSecondDifferenceQuotient_tendsto u hu)

end DOZZ.Proofs
