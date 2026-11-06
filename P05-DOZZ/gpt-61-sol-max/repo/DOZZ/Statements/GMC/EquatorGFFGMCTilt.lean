/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.GMCGeneralTiltLimit
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_GMC_tilt`, proved by `DOZZ.Proofs.equatorGFF_GMC_tilt`. -/

public section


namespace DOZZ

/-- Cameron–Martin for chaos functionals: tilting by any `L` in the Gaussian `L²` closure shifts
the test coordinates by `Cov(X(f), L)` and multiplies the chaos by `exp (γ c)`, where `c` is the
uniform limit of the circle-average covariance potential `x ↦ Cov(X_r(x), L)`. -/
alias equatorGFF_GMC_tilt := DOZZ.Proofs.equatorGFF_GMC_tilt

end DOZZ
