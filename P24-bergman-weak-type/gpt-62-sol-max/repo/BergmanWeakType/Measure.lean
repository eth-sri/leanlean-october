/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Normalization and support of Bergman area measures -/

public section

noncomputable section

open MeasureTheory Set Metric

namespace BergmanWeakType

instance : area.IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul volume (by positivity) ENNReal.ofReal_ne_top

theorem image_affine_disk {a b : ℂ} (hb : b ≠ 0) :
    (fun w ↦ a + b * w) '' disk = ball a ‖b‖ := by
  change ((a + ·) ∘ (b • ·)) '' ball 0 1 = _
  rw [image_comp, Metric.smul_image_ball hb]
  simp

/-- The affine chart of a Euclidean disk, with signed scale. -/
@[expose] def diskChart (a : ℂ) {R : ℝ} (hR : R ≠ 0) : ℂ ≃ᵐ ℂ :=
  (MeasurableEquiv.mulLeft₀ (R : ℂ) (Complex.ofReal_ne_zero.mpr hR)).trans (MeasurableEquiv.addLeft a)

theorem diskChart_image (a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    diskChart a hR '' disk = ball a |R| := by
  change (fun w : ℂ ↦ a + (R : ℂ) * w) '' disk = _
  simpa using image_affine_disk (a := a) (Complex.ofReal_ne_zero.mpr hR)

private theorem area_map_affine (a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    Measure.map (fun w ↦ a + (R : ℂ) * w) area = ENNReal.ofReal (R ^ 2)⁻¹ • area := by
  change area.map ((a + ·) ∘ (R • ·)) = _
  rw [← Measure.map_map (measurable_const_add a) (measurable_const_smul R), Measure.map_addHaar_smul area hR,
    Measure.map_smul _ (measurable_const_add a).aemeasurable, map_add_left_eq_self,
    Complex.finrank_real_complex, abs_of_nonneg (by positivity)]

theorem area_restrict_ball_eq_map (a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    area.restrict (ball a |R|) = ENNReal.ofReal (R ^ 2) • Measure.map (diskChart a hR) diskArea := by
  let e := diskChart a hR
  have h := e.restrict_map area (e '' disk)
  rw [e.injective.preimage_image, show area.map e = _ from area_map_affine a hR, Measure.restrict_smul] at h
  rw [← diskChart_image a hR, diskArea, ← h, smul_smul, ← ENNReal.ofReal_mul (sq_nonneg R),
    mul_inv_cancel₀ (pow_ne_zero 2 hR), ENNReal.ofReal_one, one_smul]

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk :=
  (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · filter_upwards [ae_mem_disk] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by linarith)
    apply Real.rpow_pos_of_pos
    aesop (add simp [disk])

end BergmanWeakType
