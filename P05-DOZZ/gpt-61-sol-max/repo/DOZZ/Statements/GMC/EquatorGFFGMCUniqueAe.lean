/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCUniqueAe
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_GMC_unique_ae`,
proved by `DOZZ.Proofs.equatorGFF_GMC_unique_ae`. -/

public section


namespace DOZZ

/-- Two finite random measures satisfying the same GMC predicate for the same field and parameter
agree almost surely. See [KRV, (law)]. -/
alias equatorGFF_GMC_unique_ae := DOZZ.Proofs.equatorGFF_GMC_unique_ae

end DOZZ
