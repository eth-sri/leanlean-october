/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.BetaIntegral
import Mathlib.Tactic
import BergmanWeakType.RpowRing

variable {r x : ℝ}

/-! # The real change of variables underlying boundary-circle Möbius invariance -/



noncomputable section



namespace BergmanWeakType

section
variable (r x)

def circleDenominator : ℝ := 1 + r ^ 2 - 2 * r * x

def circleMobius : ℝ :=
  (2 * r - (1 + r ^ 2) * x) / circleDenominator r x

end

section

variable (hr : |r| < 1)
include hr

theorem circleDenominator_pos (hx : x ∈ Set.Icc (-1 ) 1) :
    0 < circleDenominator r x := by
  obtain ⟨hr₁, hr₂⟩ := abs_lt.mp hr
  unfold circleDenominator
  by_cases h : 0 ≤ r <;> simp_all <;> nlinarith

theorem circleMobius_one : circleMobius r 1 = -1 := by
  apply (div_eq_iff (circleDenominator_pos hr ⟨by norm_num, le_rfl⟩).ne').mpr
  unfold circleDenominator
  ring

theorem circleMobius_neg_one : circleMobius r (-1) = 1 := by
  apply (div_eq_iff (circleDenominator_pos hr ⟨le_rfl, by norm_num⟩).ne').mpr
  unfold circleDenominator
  ring

theorem continuousOn_circleMobius :
    ContinuousOn (circleMobius r) (Set.Icc (-1 ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by unfold circleDenominator; fun_prop)
  exact fun x hx ↦ (circleDenominator_pos hr hx).ne'

section

variable (hx : x ∈ Set.Icc (-1 ) 1)
include hx

theorem one_sub_circleMobius_sq :
    1 - circleMobius r x ^ 2 =
      (1 - r ^ 2) ^ 2 * (1 - x ^ 2) / circleDenominator r x ^ 2 := by
  have hd := (circleDenominator_pos hr hx).ne'
  unfold circleMobius
  field_simp
  unfold circleDenominator
  ring

def sqrt_one_sub_circleMobius_sq  := show Real.sqrt (1 - circleMobius r x ^ 2) = _ from 
  by
  have hr₂ : 0 < 1 - r ^ 2 := by simp_all
  rw [one_sub_circleMobius_sq hr hx, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr₂.le,
    Real.sqrt_sq (circleDenominator_pos hr hx).le]

end

theorem circleDenominator_circleMobius
    (hx : x ∈ Set.Icc (-1 ) 1) :
    circleDenominator r (circleMobius r x) =
      (1 - r ^ 2) ^ 2 / circleDenominator r x := by
  change 1 + r ^ 2 - 2 * r *
    ((2 * r - (1 + r ^ 2) * x) / circleDenominator r x) = _
  field_simp [((circleDenominator_pos hr hx).ne')]
  unfold circleDenominator
  ring


end

end BergmanWeakType
