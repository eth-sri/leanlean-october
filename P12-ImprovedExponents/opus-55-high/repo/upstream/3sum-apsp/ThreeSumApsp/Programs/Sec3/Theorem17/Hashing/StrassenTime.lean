/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.Strassen

/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/


namespace Light.Sec3

/-- The scratch space, exactly. -/
theorem strScr_add (p j : ℕ) : strScr p j + p = 4 ^ j * p := by
  induction j with
  | zero => aesop
  | succ j ih =>
    grind [strScr]

/-- The scratch space is at most the size of an operand. -/
theorem strScr_le (p j : ℕ) : strScr p j ≤ 4 ^ j * p := by
  grind [strScr_add]

variable {p q : ℕ}

/-- The scratch space grows with p. -/
theorem strScr_mono (h : p ≤ q) (j : ℕ) : strScr p j ≤ strScr q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [strScr, strScr]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

/-- The number of steps grows with p. -/
theorem strSteps_mono (h : p ≤ q) (j : ℕ) : strSteps p j ≤ strSteps q j := by
  induction j with
  | zero =>
    rw [strSteps, strSteps]
    have h2 := Nat.mul_le_mul h h
    linarith
  | succ j ih =>
    rw [strSteps, strSteps]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega
