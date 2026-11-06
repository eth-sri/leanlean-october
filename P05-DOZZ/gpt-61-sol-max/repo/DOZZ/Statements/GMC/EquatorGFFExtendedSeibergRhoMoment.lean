/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedCoulombMass
import DOZZ.GMC.Moments.RhoMoment
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_extendedSeiberg_rho_moment`,
proved by `DOZZ.Proofs.equatorGFF_extendedSeiberg_rho_moment`. -/

public section


namespace DOZZ

/-- The extended-domain moment `E[ρ^{-s}]` of [DKRV, Lemma 3.10] is strictly positive and finite
on `ExtendedSeiberg3`, i.e. well defined there. See
[KRV, (ThextendedSeibergbounds0) and (ThextendedSeibergbounds)]. -/
alias equatorGFF_extendedSeiberg_rho_moment := DOZZ.Proofs.equatorGFF_extendedSeiberg_rho_moment

end DOZZ
