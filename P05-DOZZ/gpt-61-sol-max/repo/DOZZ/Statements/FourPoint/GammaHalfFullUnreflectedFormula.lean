/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import DOZZ.FourPoint.BPZ.GammaHalfFullUnreflectedFormula
import Batteries.Tactic.Alias

/-! The statement `DOZZ.gammaHalf_full_unreflected_formula`,
proved by `DOZZ.Proofs.gammaHalf_full_unreflected_formula`. -/

public section


namespace DOZZ

/-- The full unreflected `γ/2` diagonal formula [KRV, Theorem 9.1] on its exact interval. This
includes `γ² = 2`, by continuity in `γ` at fixed nonzero `z` before any fusion limit. -/
alias gammaHalf_full_unreflected_formula := DOZZ.Proofs.gammaHalf_full_unreflected_formula

end DOZZ
