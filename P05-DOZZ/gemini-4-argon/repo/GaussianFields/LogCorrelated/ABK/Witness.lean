/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import GaussianFields.LogCorrelated.ABK.Radial

/-!
# GaussianFields.LogCorrelated/ABK/Witness

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory

namespace GaussianFields

/-! ## The scalar profile -/

/-- The piecewise-linear radial profile: `1` on `[0, 1/2]`, linearly decreasing
on `[1/2, 1]`, `0` on `[1, ∞)`. -/
@[expose]
noncomputable def abkStandardProfile (r : ℝ) : ℝ :=
  min (max (2 * (1 - r)) 0) 1

theorem abkStandardProfile_of_le_half {r} (hr : r ≤ 1 / 2) :
    abkStandardProfile r = 1 := by
  simpa [abkStandardProfile] using min_eq_right ((show (1 : ℝ) ≤ 2 * (1 - r) by linarith).trans (le_max_left _ _))

theorem abkStandardProfile_of_one_le {r} (hr : 1 ≤ r) :
    abkStandardProfile r = 0 := by
  have h1 : 2 * (1 - r) ≤ 0 := by linarith
  simp [abkStandardProfile, max_eq_right h1]

theorem abkStandardProfile_nonneg r : 0 ≤ abkStandardProfile r :=
  le_min (le_max_right _ _) zero_le_one

theorem abkStandardProfile_le_one r : abkStandardProfile r ≤ 1 :=
  min_le_right _ _

theorem lipschitzWith_abkStandardProfile : LipschitzWith 2 abkStandardProfile := by
  have hbase : LipschitzWith 2 (fun r : ℝ => 2 * (1 - r)) := by
    refine LipschitzWith.of_dist_le_mul fun r s => ?_
    rw [Real.dist_eq, Real.dist_eq, (show 2 * (1 - r) - 2 * (1 - s) = -(2 * (r - s)) by ring), abs_neg, abs_mul]
    simp
  exact (hbase.max_const 0).min_const 1

/-! ## Euclidean-norm helpers -/

/-- Reverse triangle inequality for the project Euclidean norm. -/
theorem abs_euclideanNorm_sub_euclideanNorm_le {d : Nat} (x y : Vec d) :
    |euclideanNorm x - euclideanNorm y| ≤ euclideanNorm (x - y) := by
  have hxy : y + (x - y) = x := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hyx : x + (y - x) = y := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h1 : euclideanNorm x - euclideanNorm y ≤ euclideanNorm (x - y) := by
    have := euclideanNorm_add_le y (x - y)
    rw [hxy] at this
    linarith
  have : euclideanNorm y - euclideanNorm x ≤ euclideanNorm (x - y) := by
    have := euclideanNorm_add_le x (y - x)
    rw [hyx] at this
    rw [euclideanNorm_sub_comm] at this
    linarith
  exact abs_le.mpr ⟨by linarith, h1⟩

/-! ## The standard cutoff -/

/-- The standard piecewise-linear radial ABK cutoff witness. -/
@[expose]
noncomputable def abkStandardCutoffFun (d : Nat) : Vec d → ℝ :=
  fun x => abkStandardProfile (euclideanNorm x)

theorem continuous_abkStandardCutoffFun d :
    Continuous (abkStandardCutoffFun d) :=
  lipschitzWith_abkStandardProfile.continuous.comp continuous_euclideanNorm

theorem abkStandardCutoffFun_support_subset d :
    Function.support (abkStandardCutoffFun d) ⊆ {x | euclideanNorm x ≤ 1} := by
  intro x hx
  by_contra h
  exact hx (abkStandardProfile_of_one_le (le_of_lt (by simpa using h)))

theorem hasCompactSupport_abkStandardCutoffFun d :
    HasCompactSupport (abkStandardCutoffFun d) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall (d := d) 1)
    (abkStandardCutoffFun_support_subset d)

/-- The standard witness for `ABKCutoff d`: the structure is inhabited. -/
@[expose]
noncomputable def abkStandardCutoff (d : Nat) : ABKCutoff d where
  toFun := abkStandardCutoffFun d
  continuous := continuous_abkStandardCutoffFun d
  hasCompactSupport := hasCompactSupport_abkStandardCutoffFun d
  memLp_two :=
    (continuous_abkStandardCutoffFun d).memLp_of_hasCompactSupport
      (hasCompactSupport_abkStandardCutoffFun d)
  support_subset_unitBall := abkStandardCutoffFun_support_subset d
  eq_one_of_norm_le_half := fun _ hx => abkStandardProfile_of_le_half hx
  nonneg := fun x => abkStandardProfile_nonneg _
  le_one := fun x => abkStandardProfile_le_one _
  radial := fun x y h => by simp only [abkStandardCutoffFun, h]
  lipschitz := by
    refine ⟨2, by norm_num, fun x y => ?_⟩
    have h1 : |abkStandardProfile (euclideanNorm x) -
        abkStandardProfile (euclideanNorm y)| ≤
        2 * |euclideanNorm x - euclideanNorm y| := by
      have := lipschitzWith_abkStandardProfile.dist_le_mul
        (euclideanNorm x) (euclideanNorm y)
      simpa [Real.dist_eq] using this
    have h2 := abs_euclideanNorm_sub_euclideanNorm_le x y
    calc |abkStandardCutoffFun d x - abkStandardCutoffFun d y|
        ≤ 2 * |euclideanNorm x - euclideanNorm y| := h1
      _ ≤ 2 * euclideanNorm (x - y) := by linarith

end GaussianFields

end
