/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.FourPoint.FusionAllocationAlgebra

/-! Strict exponent margins for the corrected two-rooted Taylor domain. -/

open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The time exponent retains alpha_1; it lies strictly between -1 and 0 (erratum K20, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem twoRooted_time_exponent (γ α : ℝ) (hγ : 0 < γ) (hγsq : 2 < γ ^ 2)
    (hα : γ / 2 < α) (hα2 : α < 2 / γ) :
    γ * (Q γ - α) - 2 = γ ^ 2 / 2 - γ * α ∧
      1 < γ * (Q γ - α) ∧ γ * (Q γ - α) < 2 := by
  have he : γ * (Q γ - α) = 2 + γ ^ 2 / 2 - γ * α := by
    unfold Q
    field_simp
  have hm1 : γ * α < 2 := by simpa [mul_comm] using (lt_div_iff₀ hγ).mp hα2
  have hm2 := mul_lt_mul_of_pos_left hα hγ
  rw [he]
  constructor
  · ring
  · constructor <;> nlinarith only [hγsq, hm1, hm2]

/-- The near-cluster exponent has a strictly positive extra power. -/
theorem twoRooted_near_gain (γ α : ℝ) (hγ : 0 < γ) (hα2 : α < 2 / γ) :
    2 - 2 * γ * α + (3 * γ / 2 + α - Q γ) ^ 2 / 2 =
      γ * (Q γ - α) - 2 + (α - 2 / γ) ^ 2 / 2 ∧
      0 < (α - 2 / γ) ^ 2 / 2 := by
  constructor
  · unfold Q
    field_simp
    ring
  · exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hα2.ne)) (by norm_num)

/-- The middle-region optimized moment leaves the exact positive square margin. -/
theorem twoRooted_intermediate_gain (γ α : ℝ) (_hγ : 0 < γ) (hα2 : α < 2 / γ) :
    (γ / 2 + Q γ - α) ^ 2 / 2 - γ * (Q γ - α) =
      (Q γ - α - γ / 2) ^ 2 / 2 ∧ 0 < (Q γ - α - γ / 2) ^ 2 / 2 := by
  have hdiff : 0 < Q γ - α - γ / 2 := by unfold Q; linarith only [hα2]
  exact ⟨by ring, div_pos (sq_pos_of_pos hdiff) (by norm_num)⟩

end DOZZ.Proofs
