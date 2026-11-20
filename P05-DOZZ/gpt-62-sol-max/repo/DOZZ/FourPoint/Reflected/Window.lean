/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q
import Mathlib.Tactic

/-! # The full reflected charge window

Algebraic bounds for the window. No upper bound `ξ < 1/2` is used.
-/

public section

namespace DOZZ.Proofs

/-- The reflected charge changes the zero-mode order by the reflection exponent. -/
theorem reflected_zero_mode_order (γ α₁ α₂ α₃ : ℝ) :
    ((2 * Q γ - α₁ - γ / 2) + α₂ + α₃ - 2 * Q γ) / γ =
      (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ +
        2 * (Q γ - α₁) / γ := by
  ring

end DOZZ.Proofs
