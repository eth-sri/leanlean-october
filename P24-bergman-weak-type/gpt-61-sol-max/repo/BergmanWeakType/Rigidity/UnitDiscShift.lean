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
public import Mathlib.Tactic

/-!
# Shift on the unit disc

In this file we define `Complex.UnitDisc.shift z` to be the automorphism of the unit disc
that sends `0` to `z` and preserves the diameter joining `0` to `z`.

We also prove basic properties of this function.
-/


open scoped ComplexConjugate

noncomputable section

namespace Complex.UnitDisc

public section

lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

end

/-- Auxiliary disk automorphism. -/
def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w ) / (1 + conj ↑z * w)) <| by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (shift_den_ne_zero z w)),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h := mul_pos (sub_pos.mpr z.sq_norm_lt_one) (sub_pos.mpr w.sq_norm_lt_one)
    simp [Complex.sq_norm, Complex.normSq_apply] at h ⊢
    nlinarith

theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  apply coe_injective
  have hd := shift_den_ne_zero (-z) (shiftFun z w)
  simp only [shiftFun, coe_mk] at hd ⊢
  rw [div_eq_iff hd]
  simp
  field [(by
    simpa only [mul_comm] using! shift_den_ne_zero z w
  )]

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

@[simp]
theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by ext1; simp [coe_shift]

@[simp]
theorem shift_eq_zero_iff {z w : 𝔻} : shift z w = 0 ↔ w = -z := by
  rw [← (shift z).eq_symm_apply]
  simp [shift, shiftFun]



end

end UnitDisc

end Complex
