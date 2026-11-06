/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/UnitDisc/Shift.lean
-/

module
public import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# Shift on the unit disc

In this file we define `Complex.UnitDisc.shift z` to be the automorphism of the unit disc
that sends `0` to `z` and preserves the diameter joining `0` to `z`.

We also prove basic properties of this function.
-/

open Set Function Metric
open scoped ComplexConjugate

noncomputable section

namespace Complex.UnitDisc

public section

lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

end

theorem norm_shiftFun_le (z w : 𝔻) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤ (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [norm_def, norm_def, ← Real.sqrt_mul, normSq_apply, normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm := {apply le_of_eq; simp; ring})
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using shift_den_ne_zero z w

/-- Auxiliary definition for `shift` below. This function is not a part of the public API. -/
def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    refine (norm_shiftFun_le _ _).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one]

theorem coe_shiftFun (z w : 𝔻) : (shiftFun z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

theorem shiftFun_eq_iff {z w u : 𝔻} : shiftFun z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← coe_inj, coe_shiftFun, div_eq_iff (shift_den_ne_zero _ _)]
  ring_nf

theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff, coe_shiftFun, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w

public section

/-- The automorphism of the unit disc that sends zero to `z`. -/
def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv := by
    intro w
    simpa using shiftFun_neg_apply_shiftFun (-z) w

/-- An explicit formula for `shift z w`.

Note that the definition of `shift` is not exposed, so this is not a `dsimp` lemma. -/
theorem coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := by rfl

theorem shift_eq_iff {z w u : 𝔻} : shift z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w :=
  shiftFun_eq_iff

theorem symm_shift (z : 𝔻) : (shift z).symm = shift (-z) := by
  ext1
  rfl

@[simp]
theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by simp [shift_eq_iff]

@[simp]
theorem shift_eq_zero_iff {z w : 𝔻} : shift z w = 0 ↔ w = -z := by
  rw [← Equiv.eq_symm_apply, symm_shift, shift_apply_zero]

@[simp]
theorem shift_neg_apply_self (z : 𝔻) : shift (-z) z = 0 := by simp

@[simp]
theorem shift_neg_apply_shift (z w : 𝔻) : shift (-z) (shift z w) = w := by
  rw [← symm_shift, Equiv.symm_apply_apply]

end

end UnitDisc

end Complex
