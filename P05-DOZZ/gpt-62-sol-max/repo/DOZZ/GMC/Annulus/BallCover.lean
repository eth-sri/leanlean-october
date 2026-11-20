/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.LocalScale
public import Mathlib.Data.Finset.Max
public import DOZZ.MeasureTheory.PowerSums

/-!
# Fixed-shape covers for GMC annuli

An outer annulus of scale epsilon can be covered by finitely many balls of that same
scale. A fixed cover is chosen once on the radius-two reference disk. Moving the centers
through a compact set and a bounded radius interval preserves compactness. Positive
moments use a finite-sum estimate, without independence of the covered masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

end DOZZ.Proofs
