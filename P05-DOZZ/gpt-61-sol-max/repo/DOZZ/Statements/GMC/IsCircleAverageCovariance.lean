/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.CircleAverage
import Batteries.Tactic.Alias

/-! The statement `DOZZ.isCircleAverage_covariance`,
proved by `DOZZ.Proofs.isCircleAverage_covariance`. -/

public section


namespace DOZZ

/-- Covariance of two circle averages, for every witness of `IsCircleAverage`. -/
alias isCircleAverage_covariance := DOZZ.Proofs.isCircleAverage_covariance

end DOZZ
