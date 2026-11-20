/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.ChangeOfVariables
public import BergmanWeakType.Kernel

/-! # Similarities of the disk and their Jacobian -/
@[expose] public section
noncomputable section
open Metric MeasureTheory Set
open scoped ENNReal
namespace BergmanWeakType

theorem image_affine_disk {a b : ℂ} (hb : b ≠ 0) :
    (fun w ↦ a + b * w) '' disk = ball a ‖b‖ := by
  ext z
  constructor
  · aesop
  · intro hz
    refine ⟨(z - a) / b, ?_, ?_⟩
    · simp_all [mem_disk_iff, disk, norm_div, div_lt_one, norm_pos_iff.mpr, mem_ball_iff_norm.mp]
    · grind

/-- A nondegenerate complex affine map, as a measurable equivalence. -/
def affineMeasurableEquiv (a b : ℂ) (hb : b ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun w := a + b * w
  invFun z := (z - a) / b
  left_inv w := by simp_all
  right_inv z := by grind
  measurable_toFun := by measurability
  measurable_invFun := by measurability

section
variable {a b : ℂ} (hb : b ≠ 0)
include hb
local notation "e" => affineMeasurableEquiv a b hb
local notation "B" => ball a ‖b‖
local notation "c" => ENNReal.ofReal (‖b‖ ^ 2)

theorem affine_deriv (w : ℂ) : deriv e w = b := by
  change deriv (fun z ↦ a + b*z) w = b; simp

theorem ball_area : area.restrict B = c • Measure.map e diskArea := by
  have he : DifferentiableOn ℂ e disk := by change DifferentiableOn ℂ (fun z ↦ a+b*z) disk; fun_prop
  rw [← show e '' disk = B from image_affine_disk hb, area_image_eq_map (U := disk)  isOpen_ball he (e).injective.injOn]
  simp_rw [affine_deriv hb]
  rw [withDensity_const, Measure.map_smul _ (e).measurable.aemeasurable]; rfl

end
end BergmanWeakType
