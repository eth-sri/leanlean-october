module

public import Chazelle.Core.ReductionNow3
public import Chazelle.Core.SweepIoMain
public import Chazelle.Core.SweepEvRest
public import Chazelle.Core.SweepIoCand1
public import Chazelle.Core.SweepIoBrute
public import Chazelle.Core.SweepEvKey2Main
public import Chazelle.Core.SweepEvWin
public import Chazelle.Core.SweepEvStepL
public import Chazelle.Core.SweepIoCand0Main
public import Chazelle.Core.SweepIoS0CandFinal
public import Chazelle.Core.SweepIoLab0
public import Chazelle.Core.SweepEvLoopStart
public import Chazelle.Core.SweepEvStopLoop
public import Chazelle.Core.SweepEvStopSort6
public import Chazelle.Core.SweepEvStopRF
public import Chazelle.Core.SweepEvStopM1C5
public import Chazelle.Core.SweepEvStopM2C3

/-!
# The reduction of the target to the last open sweep pieces

The down phase is proved (`linear_of_sweep`), the sweep is assembled from stages 2–3
(`SweepEv.sweepEvSpec_of_rest`) and the answers (`SweepIo.sweepSpecH_of`, with the side-1
candidates `SweepIo.cand1Spec SweepIo.bruteSpec`).  What remains: five stage-2/3 pieces and the
side-0 candidates (`linear_of_open`).
-/

namespace Chazelle.Core

public section

/-- **Reduction of the main theorem** to the open pieces of the sweep. -/
theorem linear_of_open (hStop : SweepEv.StopTask) (hWin : SweepEv.WinTask)
    (hKey : SweepEv.KeyTask) (hL0 : SweepEv.LoopStartTask) (hL1 : SweepEv.StepTask)
    (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_sweep (SweepIo.sweepSpecH_of (SweepEv.sweepEvSpec_of_rest hStop hWin hKey hL0 hL1) h0
    (SweepIo.cand1Spec SweepIo.bruteSpec))

/-- **Reduction of the main theorem** after the window (`SweepEv.winTask`) and the next key
(`SweepEv.keyTask`): the stops, the start of the loop, one iteration and the side-0 candidates. -/
theorem linear_of_rest (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask)
    (hL1 : SweepEv.StepTask) (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_open hStop SweepEv.winTask SweepEv.keyTask hL0 hL1 h0

/-- **Reduction of the main theorem** after one iteration (`SweepEv.stepTask`): the stops, the
start of the loop and the side-0 candidates. -/
theorem linear_of_three (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask)
    (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_rest hStop hL0 SweepEv.stepTask h0

/-- **Reduction of the main theorem** after the side-0 candidates (`SweepIo.cand0Spec_of` with
`SweepIo.s0CandSpec` and `SweepIo.lab0`): the stops and the start of the loop. -/
theorem linear_of_two (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask) :
    LinearTimeTriangulation :=
  linear_of_three hStop hL0 (SweepIo.cand0Spec_of SweepIo.s0CandSpec SweepIo.lab0)

/-- **Reduction of the main theorem to the stops** (`SweepEv.StopTask`), the last open piece
of the sweep. -/
theorem linear_of_stops (hStop : SweepEv.StopTask) : LinearTimeTriangulation :=
  linear_of_two hStop SweepEv.loopStartTask

/-- **Reduction of the main theorem** to the per-origin step of the stops and their sort. -/
theorem linear_of_org_sort (hO : SweepEv.OrgTask) (hS : SweepEv.SortTask) :
    LinearTimeTriangulation :=
  linear_of_stops (SweepEv.stopTask_of hO hS)

/-- **Reduction of the main theorem to the per-origin step of the stops** (`SweepEv.OrgTask`),
the sort being proved (`SweepEv.sortTask`). -/
theorem linear_of_org (hO : SweepEv.OrgTask) : LinearTimeTriangulation :=
  linear_of_org_sort hO SweepEv.sortTask

/-- **Reduction of the main theorem to the final step of a stop origin** (`SweepEv.FinTask`):
the per-origin step is `SweepEv.orgTask_of'` with the two candidates `SweepEv.m2Task`,
`SweepEv.m1Task`. -/
theorem linear_of_fin (hF : SweepEv.FinTask) : LinearTimeTriangulation :=
  linear_of_org (SweepEv.orgTask_of' SweepEv.m2Task SweepEv.m1Task hF)

end

end Chazelle.Core
