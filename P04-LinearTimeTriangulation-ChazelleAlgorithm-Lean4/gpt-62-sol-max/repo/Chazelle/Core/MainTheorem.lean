module

public import Chazelle.Core.ReductionNow4
public import Chazelle.Core.SweepEvStopFin8

/-!
# The main theorem

Linear-time triangulation (Chazelle's theorem), by the program of this development, assembled:
the reduction `linear_of_fin` (down phase, up phase, sweep and stops all proved) applied to the
last step of a stop origin `SweepEv.finTask`.
-/

namespace Chazelle.Core

public section

/-- **Linear-time triangulation of a simple polygon** (Chazelle). -/
theorem linearTimeTriangulation : LinearTimeTriangulation :=
  linear_of_fin SweepEv.finTask

end

end Chazelle.Core
