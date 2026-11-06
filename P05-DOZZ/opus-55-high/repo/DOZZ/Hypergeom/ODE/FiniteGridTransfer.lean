/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Basic

/-! A finite grid of commuting local continuation squares has path-independent boundary transfer
between its fixed endpoints. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*}

/-- Apply `n` horizontal continuation steps, beginning at column `i` on row `j`. -/
def finiteGridHorizontal (right : ℕ → ℕ → E → E) (i j : ℕ) : ℕ → E → E
  | 0, y => y
  | n + 1, y => right (i + n) j (finiteGridHorizontal right i j n y)

/-- Apply `m` vertical continuation steps, beginning at column `i` and row `j`. -/
def finiteGridVertical (up : ℕ → ℕ → E → E) (i j : ℕ) : ℕ → E → E
  | 0, y => y
  | m + 1, y => up i (j + m) (finiteGridVertical up i j m y)

end DOZZ.Proofs
