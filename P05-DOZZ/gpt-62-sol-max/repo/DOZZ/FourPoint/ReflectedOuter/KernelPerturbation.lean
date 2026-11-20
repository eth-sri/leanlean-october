/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Relative kernel perturbation on the retained region -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Powers between zero and two are uniformly Lipschitz on the interval `[1/2,2]`. -/
theorem reflected_rpow_near_one (b t : ℝ) (hb : 0 ≤ b) (hb₂ : b ≤ 2)
    (ht : 1 / 2 ≤ t) (ht₂ : t ≤ 2) : |t ^ b - 1| ≤ 4 * |t - 1| := by
  have hd : ∀ s ∈ Icc (1 / 2 : ℝ) 2,
      HasDerivAt (fun y : ℝ => y ^ b) (b * s ^ (b - 1)) s := by
    intro s hs
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith only [hs.1]))
  have hh : ∀ s ∈ Icc (1 / 2 : ℝ) 2, ‖deriv (fun y : ℝ => y ^ b) s‖ ≤ 4 := by
    intro s hs
    have hsp : 0 < s := by linarith only [hs.1]
    have he : |b - 1| ≤ 1 := abs_le.mpr ⟨by linarith only [hb], by linarith only [hb₂]⟩
    have hpow : s ^ (b - 1) ≤ 2 := by
      have hbound := coulombWeight_rpow_le (L := 2) (by norm_num)
        (by norm_num; exact hs.1) hs.2 (b - 1)
      exact hbound.trans (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    rw [(hd s hs).deriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb,
      abs_of_pos (Real.rpow_pos_of_pos hsp _)]
    nlinarith only [hb, hb₂, hpow]
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hh (convex_Icc (1 / 2 : ℝ) 2)
    (show (1 : ℝ) ∈ Icc (1 / 2) 2 by norm_num) (show t ∈ Icc (1 / 2) 2 from ⟨ht, ht₂⟩)
  simpa only [Real.one_rpow, Real.norm_eq_abs] using hm

/-- The perturbed kernel factors through the ratio of its two distances. -/
theorem reflected_kernel_distance_ratio (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (hx : 0 < ‖x‖) :
    gammaHalfKernel γ α₁ α₂ α₃ z x =
      (‖x - z‖ / ‖x‖) ^ (γ ^ 2 / 2) * gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
  have hn : ‖x‖ ^ (γ ^ 2 / 2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  unfold gammaHalfKernel
  rw [sub_zero, Real.div_rpow (norm_nonneg _) hx.le]
  field_simp

/-- Lower and first-order bounds for the ratio of the shifted and unshifted radial powers. -/
private theorem radial_ratio_bounds (b : ℝ) (hb : 0 ≤ b) (hb₂ : b ≤ 2)
    (x z : ℂ) (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    (1 / 4 : ℝ) ≤ (‖x - z‖ / ‖x‖) ^ b ∧
      |(‖x - z‖ / ‖x‖) ^ b - 1| ≤ 4 * (‖z‖ / ‖x‖) := by
  let t := ‖x - z‖ / ‖x‖
  have hlo : 1 / 2 ≤ t := (le_div_iff₀ hx).mpr (by linarith [norm_sub_norm_le x z])
  have hhi : t ≤ 2 := (div_le_iff₀ hx).mpr (by linarith [norm_sub_le x z])
  have htd : |t - 1| ≤ ‖z‖ / ‖x‖ := by
    dsimp only [t]
    rw [div_sub_one hx.ne', abs_div, abs_of_pos hx]
    apply div_le_div_of_nonneg_right _ hx.le
    simpa only [sub_sub_cancel_left, norm_neg] using abs_norm_sub_norm_le (x - z) x
  refine ⟨?_, (reflected_rpow_near_one b t hb hb₂ hlo hhi).trans
    (mul_le_mul_of_nonneg_left htd (by norm_num))⟩
  calc
    _ = (1 / 2 : ℝ) ^ (2 : ℝ) := by norm_num
    _ ≤ (1 / 2 : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hb₂
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) hlo hb

/-- A moving mass is close to its base mass with additive error `d * S`, and is
bounded below by a quarter of the base mass. -/
structure RelativeMassBound (d : ℝ) (S T : ℝ≥0∞) : Prop where
  lower : ENNReal.ofReal (1 / 4 : ℝ) * S ≤ T
  upper : T ≤ S + ENNReal.ofReal d * S
  reverse : S ≤ T + ENNReal.ofReal d * S

/-- A common distance-ratio estimate for the exterior moving kernels. -/
theorem exterior_kernel_relative_mass (b : ℝ) (hb : 0 ≤ b) (hb₂ : b ≤ 2)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hz : ‖z‖ ≤ r / 2) (μ : Measure ℂ)
    (F G : ℂ → ℝ) (hF : Measurable F) (hG : Measurable G) (hF₀ : ∀ x, 0 ≤ F x)
    (hmove : ∀ x, 0 < ‖x‖ → G x = (‖x - z‖ / ‖x‖) ^ b * F x) :
    RelativeMassBound (4 * (‖z‖ / r))
      (∫⁻ x in {x : ℂ | r ≤ ‖x‖}, ENNReal.ofReal (F x) ∂μ)
      (∫⁻ x in {x : ℂ | r ≤ ‖x‖}, ENNReal.ofReal (G x) ∂μ) := by
  let d := 4 * (‖z‖ / r)
  let D : Set ℂ := {x | r ≤ ‖x‖}
  let K₀ := fun x => ENNReal.ofReal (F x)
  let K := fun x => ENNReal.ofReal (G x)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hK₀ : Measurable K₀ := ENNReal.measurable_ofReal.comp hF
  have hK : Measurable K := ENNReal.measurable_ofReal.comp hG
  have hp (x : ℂ) (hx : x ∈ D) : RelativeMassBound d (K₀ x) (K x) := by
    have hx' : 0 < ‖x‖ := hr.trans_le hx
    obtain ⟨hl, he⟩ := radial_ratio_bounds b hb hb₂ x z hx'
      (hz.trans (div_le_div_of_nonneg_right hx (by norm_num)))
    have hmul := hmove x hx'
    have hl' := mul_le_mul_of_nonneg_right hl (hF₀ x)
    have hG₀ : 0 ≤ G x := by
      rw [hmul]
      exact mul_nonneg (Real.rpow_nonneg (div_nonneg (norm_nonneg _) hx'.le) _) (hF₀ x)
    have hε : |G x - F x| ≤ d * F x := by
      rw [hmul, ← sub_one_mul, abs_mul, abs_of_nonneg (hF₀ x)]
      exact mul_le_mul_of_nonneg_right (he.trans
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (norm_nonneg _) hr hx) (by norm_num))) (hF₀ x)
    obtain ⟨hlow, hhigh⟩ := abs_le.mp hε
    constructor <;> dsimp only [K, K₀]
    · rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), hmul]
      exact ENNReal.ofReal_le_ofReal hl'
    · rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_add (hF₀ x) (mul_nonneg hd (hF₀ x))]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_add hG₀ (mul_nonneg hd (hF₀ x))]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  change RelativeMassBound d (∫⁻ x in D, K₀ x ∂μ) (∫⁻ x in D, K x ∂μ)
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hD fun x hx => (hp x hx).lower
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hK₀]
    exact setLIntegral_mono' hD fun x hx => (hp x hx).upper
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hK]
    exact setLIntegral_mono' hD fun x hx => (hp x hx).reverse

end DOZZ.Proofs
