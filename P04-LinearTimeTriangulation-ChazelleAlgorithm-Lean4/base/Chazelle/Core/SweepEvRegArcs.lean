module

public import Chazelle.Core.SweepEvTasks4
public import Chazelle.Core.SweepEvGenM

/-!
# Sweep, stage 3: arcs per region (`RegArcsTask`)

Every region record of a valid normal form of a simple chain has at most `D + 1` arcs when the
family has degree at most `D` (the first half of `SweepEv.region_bounds`).
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- **`RegArcsTask`**: at most `D + 1` arcs per region. -/
theorem regArcsTask : RegArcsTask := fun _ _ _ _ hP hNF hdeg =>
  (region_bounds hP hNF hdeg).1

end

end SweepEv

end Chazelle.Core
