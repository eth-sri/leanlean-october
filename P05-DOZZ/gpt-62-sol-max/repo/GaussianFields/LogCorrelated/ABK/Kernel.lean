/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ConvolutionBounds

/-!
# GaussianFields ABK scale kernel

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The ABK deterministic product-coordinate kernel before composing with the scale-space split. -/
@[expose]
noncomputable def abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) : ℝ × Vec d → ℝ :=
  fun p =>
    if 0 < p.1 then
      normalization *
        p.1 ^ (-(((d : ℝ) + 1) / 2)) *
          abkSpatialConvolution ζ ψ p.1 p.2
    else
      0

/-- Every spatial section of the squared ABK product kernel is integrable. -/
theorem integrable_sq_abkLogKernelProd_section {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (r : ℝ) :
    Integrable
      (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  by_cases hr : 0 < r
  · simpa only [abkLogKernelProd, ite_eq_left hr, mul_pow] using
      (integrable_sq_abkSpatialConvolution ζ ψ hr).const_mul
        (normalization ^ (2 : Nat) * (r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat))
  · simp [abkLogKernelProd, hr]

/-- The ABK product-coordinate kernel is a.e.-strongly measurable for any ambient measure. -/
theorem aestronglyMeasurable_abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (μ : Measure (ℝ × Vec d)) :
    AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ) μ := by
  unfold abkLogKernelProd
  apply Measurable.aestronglyMeasurable
  exact (((measurable_fst.pow_const _).const_mul normalization).mul
    (stronglyMeasurable_abkSpatialConvolution_prod ζ ψ).measurable).ite
      (measurableSet_lt measurable_const measurable_fst) measurable_const

/-- The square of the ABK product-coordinate kernel is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_sq_abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (μ : Measure (ℝ × Vec d)) :
    AEStronglyMeasurable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) μ :=
  (aestronglyMeasurable_abkLogKernelProd normalization ζ ψ μ).pow 2

theorem abkLogKernelProd_mul {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (p : ℝ × Vec d) :
    abkLogKernelProd normalization ζ ψ p *
        abkLogKernelProd normalization ζ φ p =
      if 0 < p.1 then
        normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
          (abkSpatialConvolution ζ ψ p.1 p.2 *
            abkSpatialConvolution ζ φ p.1 p.2)
      else
        0 := by
  by_cases hr : 0 < p.1
  · have hpref : (p.1 ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) =
        p.1 ^ (-((d : ℝ) + 1)) := by
      rw [← Real.rpow_mul_natCast hr.le]
      congr 1
      norm_num
    simp only [abkLogKernelProd, ite_eq_left hr, ← hpref]
    ring
  · simp [abkLogKernelProd, hr]

/-- Integrating the squared product kernel factors out its deterministic prefactor. -/
private theorem integral_norm_sq_abkLogKernelProd_section_eq {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) =
      normalization ^ (2 : Nat) * r ^ (-((d : ℝ) + 1)) *
        ∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖ := by
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [pow_two, abkLogKernelProd_mul, ite_eq_left hr, norm_mul,
    Real.norm_of_nonneg (by positivity), ← pow_two]

private theorem integral_norm_sq_abkLogKernelProd_le {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r C a : ℝ} (hr : 0 < r)
    (h : (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖) ≤ C * r ^ a) :
    (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) ≤
      (normalization ^ (2 : Nat) * C) * r ^ (a - ((d : ℝ) + 1)) := by
  rw [integral_norm_sq_abkLogKernelProd_section_eq normalization ζ ψ hr]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  rw [show normalization ^ (2 : Nat) * r ^ (-((d : ℝ) + 1)) * (C * r ^ a) =
    (normalization ^ (2 : Nat) * C) * (r ^ a * r ^ (-((d : ℝ) + 1))) by ring,
    ← Real.rpow_add hr, sub_eq_add_neg]

/-- The squared product kernel is bounded by `C r^(d-1)` at small scales. -/
theorem integral_norm_sq_abkLogKernelProd_le_small {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) ≤
        C * r ^ ((d : ℝ) - 1) := by
  obtain ⟨C, hC, h⟩ := integral_norm_sq_abkSpatialConvolution_le_small ζ ψ
  refine ⟨normalization ^ (2 : Nat) * C, by positivity, fun r hr h₁ => ?_⟩
  have hsp := h r hr h₁ (integrable_sq_abkSpatialConvolution ζ ψ hr)
  rw [← Real.rpow_natCast r (2 * d), Nat.cast_mul, Nat.cast_ofNat] at hsp
  simpa only [show 2 * (d : ℝ) - ((d : ℝ) + 1) = d - 1 by ring] using
    integral_norm_sq_abkLogKernelProd_le normalization ζ ψ hr hsp

/-- The squared product kernel is bounded by `C r^-3` at large scales. -/
theorem integral_norm_sq_abkLogKernelProd_le_large {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) ≤
        C * r ^ (-3 : ℝ) := by
  obtain ⟨C, hC, h⟩ := integral_norm_sq_abkSpatialConvolution_le_large ζ ψ
  refine ⟨normalization ^ (2 : Nat) * C, by positivity, fun r h₁ => ?_⟩
  have hr := zero_lt_one.trans_le h₁
  have hsp := h r h₁ (integrable_sq_abkSpatialConvolution ζ ψ hr)
  have hp : r ^ (d : ℝ) * |r|⁻¹ ^ (2 : Nat) = r ^ ((d : ℝ) - 2) := by
    rw [Real.rpow_sub hr, Real.rpow_two, abs_of_pos hr, inv_pow, div_eq_mul_inv]
  rw [mul_assoc, ← Real.rpow_natCast r d, hp] at hsp
  simpa only [show (d : ℝ) - 2 - ((d : ℝ) + 1) = -3 by ring] using
    integral_norm_sq_abkLogKernelProd_le normalization ζ ψ hr hsp

end GaussianFields

end
