/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.DomainGap
public import BergmanWeakType.WeightedSharp

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter
open scoped ComplexConjugate Topology ENNReal

namespace BergmanWeakType

section
variable {a b : ℂ} (hb : b ≠ 0)
include hb
local notation "e" => affineMeasurableEquiv a b hb
local notation "B" => ball a ‖b‖
local notation "c" => ENNReal.ofReal (‖b‖ ^ 2)

private theorem affine_chart : Chart disk B e := by
  refine ⟨isOpen_ball, isOpen_ball, ?_, (by grind [affine_deriv])⟩
  rw [← image_affine_disk hb]; exact (e).injective.injOn.bijOn_image

/-- The positive Bergman operator commutes with similarities after pulling back its input. -/
private theorem IsBergmanKernel.positive_affine {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel B K)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ disk) :
    domainPositiveProjection B K f (e z) = positiveProjection (f ∘ e) z := by
  rw [domainPositiveProjection, ball_area hb, lintegral_smul_measure,
    (e).measurableEmbedding.lintegral_map, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_disk] with w hw
  have h := congrArg norm ((affine_chart hb).disk_jacobian_formula hK hz hw)
  simp only [affine_deriv, norm_smul, norm_mul, norm_div, Real.norm_eq_abs, abs_sq] at h
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), h, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hb)]
  rfl

/-- Similarity scales the level-set measure and input mass by exactly the same
factor. The pullback bijection on inputs therefore preserves the *optimal* bound. -/
private theorem affine_constant {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel B K) :
    weakTypeConstant (area.restrict B) (domainPositiveProjection B K) =
      weakTypeConstant diskArea positiveProjection := by
  have lev f t : diskArea (e ⁻¹' {z | ENNReal.ofReal t < domainPositiveProjection B K f z}) =
      diskArea {z | ENNReal.ofReal t < positiveProjection (f ∘ e) z} :=
    measure_congr (ae_mem_disk.mono (by grind [hK.positive_affine]))
  unfold weakTypeConstant; congr 1; ext C
  change IsWeakTypeBound _ _ _ ↔ IsWeakTypeBound _ _ _
  simp only [IsWeakTypeBound, ball_area hb, integrable_smul_measure (by positivity : c ≠ 0) ENNReal.ofReal_ne_top,
    (e).measurableEmbedding.integrable_map_iff, Measure.smul_apply, (e).map_apply, lev,
    lintegral_smul_measure, (e).measurableEmbedding.lintegral_map, smul_eq_mul, mul_left_comm _ c,
    ENNReal.mul_le_mul_iff_right (by positivity : c ≠ 0) ENNReal.ofReal_ne_top]
  constructor
  · intro h f; simpa [Function.comp_def] using h (f ∘ (e).symm)
  · grind [diskArea]

end

/-- Every Euclidean disk has positive Bergman weak type constant one. -/
theorem weakTypeConstant_domainPositiveProjection_ball_eq_one (a : ℂ) {R : ℝ} (hR : 0 < R)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel (ball a R) K) :
    weakTypeConstant (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) = 1 := by
  have hnorm : ‖(R : ℂ)‖ = R := by simp [hR.le]
  rw [← hnorm] at hK ⊢
  exact (affine_constant (Complex.ofReal_ne_zero.mpr hR.ne') hK).trans positiveProjection_constant_eq_one

end BergmanWeakType
