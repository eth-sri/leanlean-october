/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Monotonicity estimates for the logarithmic coefficient-height ratios. -/

public section
namespace CCDN

lemma weighted_exp_ratio_le {u v a r : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 0 < a) (hr : 1 ≤ r) (hra : 1 ≤ r * a) :
    (v + a) / Real.exp v ≤ r * ((u + a) / Real.exp u) := by
  have hru : 1 ≤ r * (u + a) := by nlinarith
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simp_all [add_comm, Real.add_one_le_exp]
  have hh : v + a ≤ r * (u + a) * Real.exp (v - u) := by
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).mpr
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hh'
  exact hh'

end CCDN
