/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import BergmanWeakType.Derivative

variable {ε c x : ℝ}

/-! # A smooth nonnegative approximation to truncation by a level -/



noncomputable section




namespace BergmanWeakType

section
variable (ε c x)

/-- A smooth approximation to `min x c`, shifted to stay nonnegative for nonnegative inputs. -/
def smoothCap : ℝ :=
  (x + c - Real.sqrt ((x - c) ^ 2 + ε ^ 2) + ε) / 2

/-- The derivative of the smooth truncation with respect to its input. -/
def smoothCapInputDeriv : ℝ :=
  (1 - (x - c) / Real.sqrt ((x - c) ^ 2 + ε ^ 2)) / 2

/-- The second input derivative of the smooth cap. -/
def smoothCapSecondDeriv : ℝ :=
  -ε ^ 2 / (2 * Real.sqrt ((x - c) ^ 2 + ε ^ 2) ^ 3)

end

theorem smoothCap_zero (c x : ℝ) : smoothCap 0 c x = min x c := by
  simp [smoothCap, Real.sqrt_sq_eq_abs]
  grind [abs_of_nonneg, abs_of_nonpos]

theorem smoothCapInputDeriv_nonneg (ε) : 0 ≤ smoothCapInputDeriv ε c x :=
  by
  unfold smoothCapInputDeriv
  bound [Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (a := (x - c) ^ 2) (sq_nonneg ε))]

@[fun_prop] theorem hasDerivAt_smoothCap_input  (hε : 0 < ε) :
    HasDerivAt (smoothCap ε c) (smoothCapInputDeriv ε c x) x := by
  unfold smoothCap smoothCapInputDeriv
  differentiate

@[fun_prop] theorem hasDerivAt_smoothCapInputDeriv  (hε : 0 < ε) :
    HasDerivAt (smoothCapInputDeriv ε c)
      (smoothCapSecondDeriv ε c x) x := by
  have hp : 0 ≤ (x - c) ^ 2 + ε ^ 2 := by positivity
  unfold smoothCapSecondDeriv smoothCapInputDeriv
  differentiate <;> grind

end BergmanWeakType
