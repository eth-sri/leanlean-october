/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.EquatorGFFChaosTransportLaw
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_GMC_law_transport`,
proved by `DOZZ.Proofs.equatorGFF_GMC_law_transport`. -/

public section


namespace DOZZ

/-- Characterization transport: two equator GFF models with `IsGMCOf` chaoses at the same
`0 < γ < 2`, on arbitrary probability spaces, have the same joint law of test evaluations and
chaos. -/
alias equatorGFF_GMC_law_transport := DOZZ.Proofs.equatorGFF_GMC_law_transport

end DOZZ
