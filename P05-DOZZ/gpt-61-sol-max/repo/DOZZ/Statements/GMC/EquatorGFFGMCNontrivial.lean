/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCIntensityAdapter
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_GMC_nontrivial`,
proved by `DOZZ.Proofs.equatorGFF_GMC_nontrivial`. -/

public section


namespace DOZZ

/-- The GMC is nontrivial: its random measure is nonzero almost surely. See [KRV, (law)]. -/
alias equatorGFF_GMC_nontrivial := DOZZ.Proofs.equatorGFF_GMC_nontrivial

end DOZZ
