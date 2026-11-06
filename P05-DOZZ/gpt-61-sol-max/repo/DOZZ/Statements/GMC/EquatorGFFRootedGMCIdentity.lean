/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.RootedIdentity
import Batteries.Tactic.Alias

/-! The statement `DOZZ.equatorGFF_rooted_GMC_identity`,
proved by `DOZZ.Proofs.equatorGFF_rooted_GMC_identity`. -/

public section


namespace DOZZ

/-- The rooted GMC identity for every nonnegative measurable functional of the root, all test
coordinates, and the chaos measure. The translated field contains `γ G(u,·)` and the rooted
measure contains `e^{γ²G(u,·)}`. See [KRV, Corollary 12.2] (corrected; erratum K3, see
docs/ERRATA-AND-DEVIATIONS.md). -/
alias equatorGFF_rooted_GMC_identity := DOZZ.Proofs.equatorGFF_rooted_GMC_identity

end DOZZ
