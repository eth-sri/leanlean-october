/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCompactChaosLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Increasing compact tests for the full extended-real insertion singularity. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Regularize the inverse radial power while keeping the support of the compact test. -/
noncomputable def singularCompactTest (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (β : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => f x * (max ‖x‖ (1 / ((n : ℝ)+1))) ^ (-β)
  have hcont : Continuous F := f.continuous.mul
    ((continuous_norm.max continuous_const).rpow_const (fun x => Or.inl (ne_of_gt
      (lt_of_lt_of_le (by positivity : 0 < 1 / ((n : ℝ)+1)) (le_max_right _ _)))))
  have hs : HasCompactSupport F := hfc.mul_right
  let hb := hcont.bounded_above_of_compact_support hs
  exact BoundedContinuousFunction.ofNormedAddCommGroup F hcont hb.choose hb.choose_spec
section
variable (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))

theorem singular_compact_test_support (β : ℝ) (n : ℕ) :
    tsupport (singularCompactTest f hfc β n : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) :=
  tsupport_mul_subset_left
section
variable (hf : ∀ x, 0 ≤ f x) (β : ℝ)
include hf

theorem singular_compact_test_nonneg (n : ℕ) (x : ℂ) :
    0 ≤ singularCompactTest f hfc β n x :=
  mul_nonneg (hf x) (Real.rpow_nonneg (by positivity) _)

/-- The compact radial approximants increase, including at the insertion center. -/
theorem singular_compact_test_mono (hβ : 0 ≤ β) (x : ℂ) :
    Monotone (fun n => singularCompactTest f hfc β n x) := by
  intro n m hnm
  change f x * (max ‖x‖ (1 / (n+1))) ^ (-β) ≤
    f x * (max ‖x‖ (1 / (m+1))) ^ (-β)
  apply mul_le_mul_of_nonneg_left _ (hf x)
  apply Real.rpow_le_rpow_of_nonpos
    (lt_of_lt_of_le (by positivity) (le_max_right ..)) _ (neg_nonpos.mpr hβ)
  gcongr

/-- The pointwise limit is the literal ENNReal inverse power, with no convention at zero
silently replacing its infinite value. -/
theorem singular_compact_test_tendsto (x : ℂ) :
    Tendsto (fun n => ENNReal.ofReal (singularCompactTest f hfc β n x)) atTop
      (𝓝 (ENNReal.ofReal (f x) * (ENNReal.ofReal ‖x‖) ^ (-β))) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hbase : Tendsto (fun n : ℕ => ENNReal.ofReal (max ‖x‖ (1 / ((n : ℝ)+1)))) atTop
      (𝓝 (ENNReal.ofReal ‖x‖)) := by
    simpa only [max_eq_left (norm_nonneg x), Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto _ |>.comp ((tendsto_const_nhds (x := ‖x‖)).max hδ)
  have hpow : Tendsto (fun n : ℕ =>
      (ENNReal.ofReal (max ‖x‖ (1 / ((n : ℝ)+1)))) ^ (-β)) atTop
      (𝓝 _) :=
    ENNReal.continuous_rpow_const.tendsto _ |>.comp hbase
  have hprod := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (f x)) hpow
    (Or.inr ENNReal.ofReal_ne_top)
  convert hprod using 1
  funext n
  change ENNReal.ofReal (f x * (max ‖x‖ (1 / (n+1))) ^ (-β)) = _
  rw [ENNReal.ofReal_mul (hf x), ENNReal.ofReal_rpow_of_pos
    (lt_of_lt_of_le (by positivity) (le_max_right ..))]

end

end

end DOZZ.Proofs
