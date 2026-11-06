/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import DOZZ.FourPoint.ReflectedOuter.GammaHalfReflectedOuterLittleO
import Batteries.Tactic.Alias

/-! The statement `DOZZ.gammaHalf_reflected_outer_littleO`,
proved by `DOZZ.Proofs.gammaHalf_reflected_outer_littleO`. -/

public section


namespace DOZZ

/-- The reflected outer-region correction is `o(|z|^κ)`. The buffer `ξ` is required to exceed the
local fusion exponent on the stated neighborhood. -/
alias gammaHalf_reflected_outer_littleO := DOZZ.Proofs.gammaHalf_reflected_outer_littleO

end DOZZ
