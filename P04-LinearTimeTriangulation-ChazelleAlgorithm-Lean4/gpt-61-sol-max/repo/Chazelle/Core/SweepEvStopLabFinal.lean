module

public import Chazelle.Core.SweepEvStopLab4
public import Chazelle.Core.SweepEvSplitGap

/-!
# Sweep, stage 2: the side labels of the stops (`LabTask`)

`LabTask` from `SweepEv.labTask_of` and the split-tie lemma `SweepEv.splitGapTask`.
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- **`LabTask`**: the side labels of an anchored stop chord. -/
theorem labTask : LabTask := labTask_of splitGapTask

end

end SweepEv

end Chazelle.Core
