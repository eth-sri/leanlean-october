/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.Diagonal.Assembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.degenerateFourPoint_diagonal_classification`,
proved by `DOZZ.Proofs.degenerateFourPoint_diagonal_classification`. -/

public section


namespace DOZZ

/-- The normalized physical solution has the diagonal Gauss representation with its coefficient
fixed by `T(0) = C`. The physical charge domain supplies nonresonance and nonzero `K₂` (see
`DOZZ.gauss_physical_parameter_range` and `DOZZ.real_gauss_solution_physical_normalization`); the
general classification retains the guard `K₂ ≠ 0` (erratum K27, see
docs/ERRATA-AND-DEVIATIONS.md). -/
alias degenerateFourPoint_diagonal_classification := DOZZ.Proofs.degenerateFourPoint_diagonal_classification

end DOZZ
