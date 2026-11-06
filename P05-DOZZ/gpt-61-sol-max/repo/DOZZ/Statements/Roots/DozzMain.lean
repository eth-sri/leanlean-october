/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Roots.Assembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.dozz_main`, proved by `DOZZ.Proofs.dozz_main`. -/

public section


namespace DOZZ

/-- **DOZZ formula** ([KRV, Theorem 2.4]). -/
alias dozz_main := DOZZ.Proofs.dozz_main

end DOZZ
