/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import DOZZ.FourPoint.Reflected.InnerLimit
import Batteries.Tactic.Alias

/-! The statement `DOZZ.gammaHalf_reflected_inner_limit`,
proved by `DOZZ.Proofs.gammaHalf_reflected_inner_limit`. -/

public section


namespace DOZZ

/-- Exact reflected coefficient from the inner cluster, in explicit little-o form. -/
alias gammaHalf_reflected_inner_limit := DOZZ.Proofs.gammaHalf_reflected_inner_limit

end DOZZ
