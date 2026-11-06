/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitFDDMarkov

/-!
# Path support from the conditioned entrance FDDs

The explicit entrance density is supported on the strictly negative half-line at every positive
time. Countably many rational evaluations and continuity then imply that a conditioned path stays
in the closed negative half-line for all times. This argument does not assert that the path cannot
touch zero at an irrational time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs
section
variable {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
include hP


end

end DOZZ.Proofs

end
