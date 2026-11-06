/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Roots.Existence
import Batteries.Tactic.Alias

/-! The statement `DOZZ.dozz_existence`, proved by `DOZZ.Proofs.dozz_existence`. -/

public section


namespace DOZZ

/-- **Existence**: for every `0 < γ < 2` there are a probability space, an equator GFF and its
GMC (whose circle averages exist by `IsGMCOf`), and a function `Υ_{γ/2}`. -/
alias dozz_existence := DOZZ.Proofs.dozz_existence

end DOZZ
