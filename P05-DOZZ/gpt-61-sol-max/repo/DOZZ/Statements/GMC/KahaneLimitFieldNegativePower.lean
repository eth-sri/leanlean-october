/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitFieldNegativePower
import Batteries.Tactic.Alias

/-! The statement `DOZZ.kahane_limit_field_negative_power`,
proved by `DOZZ.Proofs.kahane_limit_field_negative_power`. -/

public section


namespace DOZZ

/-- Limit Kahane comparison for negative powers. Convergence in probability suffices because the
comparison passes through bounded Laplace tests; no `L¹` convergence of the masses is needed. -/
alias kahane_limit_field_negative_power := DOZZ.Proofs.kahane_limit_field_negative_power

end DOZZ
