/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.GaussianClosure
import Batteries.Tactic.Alias

/-! The statement `DOZZ.circleAverage_isGaussianProcess`,
proved by `DOZZ.Proofs.circleAverage_isGaussianProcess`. -/

public section


universe u

namespace DOZZ

/-- Joint Gaussianity and centering of every witness, see [KRV, (hatGformula)] and
[KRV, (circleav)]. -/
alias circleAverage_isGaussianProcess := DOZZ.Proofs.circleAverage_isGaussianProcess

end DOZZ
