/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedCoulombMass
import DOZZ.GMC.WeightedCutoff.Bound
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_GMC_weighted_cutoff_bound`,
proved by `DOZZ.Proofs.equatorGFF_GMC_weighted_cutoff_bound`. -/

public section


namespace DOZZ

/-- With strict weighted-moment slack, cutoff weighted masses obey the local scaling bound
uniformly over compact center sets and compact parameter sets. See [KRV, §7.2] and
[KRV, (annulus)]. -/
alias equatorGFF_GMC_weighted_cutoff_bound := DOZZ.Proofs.equatorGFF_GMC_weighted_cutoff_bound

end DOZZ
