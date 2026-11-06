/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
import Batteries.Tactic.Alias

/-! The statement `DOZZ.fourPointT_zero_eq_structureConstant`,
proved by `DOZZ.Proofs.fourPointT_zero_eq_structureConstant`. -/

public section


namespace DOZZ

/-- Fusing the degenerate insertion at zero changes the first three-point charge by `-χ`
([KRV, (Fundrelation1)]). -/
alias fourPointT_zero_eq_structureConstant := DOZZ.Proofs.fourPointT_zero_eq_structureConstant

end DOZZ
