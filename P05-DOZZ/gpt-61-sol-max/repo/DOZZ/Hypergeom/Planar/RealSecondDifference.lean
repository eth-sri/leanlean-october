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
  fun_prop (disch := positivity)

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg u) p

private theorem measurable_normPowerRealSecondDifference (k t : ℝ) :
    Measurable (fun u : ℂ => normPowerRealSecondDifference k t (u - 1)) := by
  unfold normPowerRealSecondDifference
  fun_prop (disch := positivity)

private theorem measurable_planarRealSecondDifferenceQuotient (k β t : ℝ) :
    Measurable (planarRealSecondDifferenceQuotient k β t) := by
  exact (measurable_complex_norm_rpow (-β)).mul
    (measurable_normPowerRealSecondDifference k t)

/-- A global Riesz majorant for the real second difference at nonzero steps. -/
theorem normPowerRealSecondDifference_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (x : ℂ) (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0) :
    |normPowerRealSecondDifference k t x| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) +
        (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
  let C  := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hglobal := norm_rpow_centered_difference_le_global k hk hk₂ x (t : ℂ) hx
  have htNorm : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
    simp_all
  have ht2  := sq_pos_of_ne_zero ht
  change |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k -
    2 * ‖x‖ ^ k) / t ^ 2| ≤ _
  rw [abs_div, abs_of_pos ht2]
  have hupper :
      |‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k| ≤
        (2 * C + B) * ‖(t : ℂ)‖ ^ 2 * ‖x‖ ^ (k - 2) := by
    exact hglobal
  calc
    _ ≤ ((2 * C + B) * ‖(t : ℂ)‖ ^ 2 * ‖x‖ ^ (k - 2)) / t ^ 2 :=
      div_le_div_of_nonneg_right hupper (le_of_lt ht2)
    _ = (2 * C + B) * ‖x‖ ^ (k - 2) := by
      grind
    _ = (2 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) +
        (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
          dsimp [C, B]
          ring

variable (k β : ℝ) (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)

include k β hk hβ hβ₂ in
/-- Integrability of the centered quotient at every step. -/
theorem integrable_planarRealSecondDifferenceQuotient  (t : ℝ) :
    Integrable (planarRealSecondDifferenceQuotient k β t) volume := by
  by_cases ht : t = 0
  · subst t
    have hzero : planarRealSecondDifferenceQuotient k β 0 = fun _ : ℂ => (0 : ℝ) := by
      funext u
      simp [planarRealSecondDifferenceQuotient, normPowerRealSecondDifference]
    simp_all
  · let C  := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
        (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
    let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
    
    have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
    have hboundInt : Integrable bound volume := by
      fun_prop (disch := positivity)
    have hpoint : ∀ᵐ u ∂volume,
        ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
      filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
      have hx  := sub_ne_zero.mpr hu
      have hk₂ : k < 2 := by linarith [hβ, hβ₂]
      have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
      rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hnorm]
      have hdiff := normPowerRealSecondDifference_le k hk hk₂ (u - 1) t hx ht
      have hmul := mul_le_mul_of_nonneg_left hdiff hnorm
      grind
    apply hboundInt.mono'
      (measurable_planarRealSecondDifferenceQuotient k β t).aestronglyMeasurable
    exact hpoint

/-- Pointwise second derivative limit of the weighted radial kernel. -/
theorem planarRealSecondDifferenceQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
  have hx  := sub_ne_zero.mpr hu
  let w  := ‖u‖ ^ (-β)
  have hrad := norm_rpow_real_centered_difference_tendsto k (u - 1) hx
  have hmul : Tendsto
      (fun t : ℝ => w * normPowerRealSecondDifference k t (u - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (w * ((k / 2) * (k / 2 - 1) * (‖u - 1‖ ^ 2) ^ (k / 2 - 2) *
        (2 * (u - 1).re) ^ 2 + (k / 2) * (‖u - 1‖ ^ 2) ^ (k / 2 - 1) * 2))) :=
    tendsto_const_nhds.mul hrad
  continuity

include k β hk hβ hβ₂ in
/-- Dominated convergence for the real second derivative of the normalized parent. -/
theorem planarRealSecondDifferenceQuotient_integral_tendsto  :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ u : ℂ, planarRealSecondDifferenceLimit k β u)) := by
  let C  := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  
  have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
  have hboundInt : Integrable bound volume := by
    fun_prop (disch := positivity)
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (planarRealSecondDifferenceQuotient k β t) volume := by
    filter_upwards [] with t
    exact (integrable_planarRealSecondDifferenceQuotient k β hk hβ hβ₂ t).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by exact ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    have hx  := sub_ne_zero.mpr hu
    have hk₂ : k < 2 := by linarith [hβ, hβ₂]
    have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
    rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hnorm]
    have hdiff := normPowerRealSecondDifference_le k hk hk₂ (u - 1) t hx ht0
    have hmul := mul_le_mul_of_nonneg_left hdiff hnorm
    grind
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun t : ℝ => planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    exact planarRealSecondDifferenceQuotient_tendsto k β u hu
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hbound hboundInt hlim

end DOZZ.Proofs
