/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.RbarCoefficient
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

theorem continuousAt_lFun {x : ℂ} (h1 : ∀ m : ℕ, x ≠ -m) (h2 : ∀ m : ℕ, 1 - x ≠ -m) :
    ContinuousAt lFun x := by
  exact (Complex.differentiableAt_Gamma x h1).continuousAt.div ((Complex.differentiableAt_Gamma (1 - x) h2).continuousAt.comp (continuous_const.sub continuous_id).continuousAt) (Complex.Gamma_ne_zero h2)

theorem lFun_ne_zero {x : ℂ} (h1 : ∀ m : ℕ, x ≠ -m) (h2 : ∀ m : ℕ, 1 - x ≠ -m) :
    lFun x ≠ 0 :=
  div_ne_zero (Complex.Gamma_ne_zero h1) (Complex.Gamma_ne_zero h2)

theorem ofReal_ne_neg_nat_of_mem {r : ℝ} (h : (-1 < r ∧ r < 0) ∨ (0 < r ∧ r < 1) ∨
    (1 < r ∧ r < 2)) : ∀ m : ℕ, (r : ℂ) ≠ -m := by
  intro m hm
  have hr : r = -m := by exact_mod_cast hm
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hr] at h1 h2
    rcases Nat.lt_or_ge m 1 with hm1 | hm1
    · interval_cases m
      norm_num at h2
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
  · rw [hr] at h1
    linarith
  · rw [hr] at h1
    linarith

end DOZZ.Proofs

end
