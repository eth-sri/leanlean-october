/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass
import DOZZ.Brownian.Reflection.MomentAssembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.reflectionMass_lastCut_bound`,
proved by `DOZZ.Proofs.reflectionMass_lastCut_bound`. -/

public section


namespace DOZZ

/-- The last-cut estimate for the two-sided reflection integral; it does not assume that the
discarded and retained masses are independent. -/
alias reflectionMass_lastCut_bound := DOZZ.Proofs.reflectionMass_lastCut_bound

end DOZZ
