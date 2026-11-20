/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q

/-! The unweighted annular exponent governing the positive-moment induction. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The exact-scale moment exponent `ξγ(p)`. -/
noncomputable def gmcScaleExponent (γ p : ℝ) : ℝ :=
  2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2

/-- On the physical interval the Gaussian scale exponent is `γQp - γ²p²/2`. -/
theorem gmcScaleExponent_eq_Q (γ p : ℝ) (hγ : γ ≠ 0) :
    gmcScaleExponent γ p = γ * Q γ * p - γ ^ 2 * p ^ 2 / 2 := by
  unfold gmcScaleExponent Q
  field_simp [hγ]

/-- The unweighted scaling power is positive below the moment threshold. -/
theorem gmcScaleExponent_pos {γ p : ℝ} (hp : 0 < p) (h : γ ^ 2 * p < 4) :
    0 < gmcScaleExponent γ p := by
  have hf : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by linarith [sq_nonneg γ]
  unfold gmcScaleExponent
  nlinarith only [mul_pos hp hf]

/-- The exponent of the sharp ball bound minus the insertion loss is the weighted exponent. -/
theorem sharpBallExponent_sub_insertion (γ α p : ℝ) (hγ : 0 < γ) :
    gmcScaleExponent γ p - γ * α * p =
      γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 := by
  rw [gmcScaleExponent_eq_Q γ p hγ.ne']
  ring

end DOZZ.Proofs
