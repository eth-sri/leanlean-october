/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Int

/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/


namespace ThreeSumApsp

open Classical in
/-- The answer of a decision problem as a number: 1 for yes, 0 for no. -/
noncomputable def flag (p : Prop) : ℤ := if p then 1 else 0

variable {p : Prop}

/-- The answer yes is written as 1. -/
theorem flag_of (h : p) : flag p = 1 := if_pos h

/-- The answer no is written as 0. -/
theorem flag_of_not (h : ¬ p := by simp) : flag p = 0 := if_neg h

/-- The number 1 means yes. -/
theorem flag_eq_one_iff : flag p = 1 ↔ p := by
  grind [flag_of, flag_of_not]

/-- Equivalent questions have the same answer. -/
theorem flag_congr {q : Prop} (h : p ↔ q := by grind) : flag p = flag q := by
  simp_all

/-- An answer is 0 or 1. -/
theorem flag_mem (p : Prop) : 0 ≤ flag p ∧ flag p < 2 := by
  by_cases h : p
  · grind [flag_of]
  grind [flag_of_not]
