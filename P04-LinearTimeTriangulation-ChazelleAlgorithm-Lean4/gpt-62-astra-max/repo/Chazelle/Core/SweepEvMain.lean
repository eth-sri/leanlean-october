module

public import Chazelle.Core.SweepEvRun2

/-!
# The sweep (WP-D), stages 2–3: the contract `SweepEvSpec` from its pieces

`sweepEvSpec_of`: the assembly (`AsmTask`) of the initialisation (`InitTask`) and the run steps
(`runTask_of`, from the contracts of the pieces).
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- **`SweepEvSpec` from the contracts of its pieces.** -/
theorem sweepEvSpec_of (hAsm : AsmTask) (hInit : InitTask) (hGen : GenTask) (hStop : StopTask)
    (hWin : WinTask) (hOrgs : OrgsTask) (hKey : KeyTask) (hPrep : PrepTask)
    (hL0 : LoopStartTask) (hL1 : StepTask) (hL2 : DoneTask) (hRA : RegArcsTask)
    (hC : CountTask) : SweepEvSpec :=
  hAsm hInit (runTask_of hGen hStop hWin hOrgs hKey hPrep hL0 hL1 hL2 hRA hC)

end

end SweepEv

end Chazelle.Core
