/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Roots.Assembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.dozz_unitVolume`, proved by `DOZZ.Proofs.dozz_unitVolume`. -/

public section


namespace DOZZ

/-- **Unit-volume companion**: on all of `U₃`, including `s ∈ −ℕ`, `C̄` is the limit of
`μ^s C^{DOZZ} / Γ(s)` along pole-free points of `U₃`. -/
alias dozz_unitVolume := DOZZ.Proofs.dozz_unitVolume

end DOZZ
