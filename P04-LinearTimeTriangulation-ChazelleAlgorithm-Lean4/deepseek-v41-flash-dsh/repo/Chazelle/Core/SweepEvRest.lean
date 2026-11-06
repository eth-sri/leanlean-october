module

public import Chazelle.Core.SweepEvMain
public import Chazelle.Core.SweepEvAsm
public import Chazelle.Core.SweepEvGen
public import Chazelle.Core.SweepEvOrgs2
public import Chazelle.Core.SweepEvPrep
public import Chazelle.Core.SweepEvStepDone
public import Chazelle.Core.SweepEvRegArcs
public import Chazelle.Core.SweepEvCount

/-!
# Sweep, stages 2–3: what remains

`SweepEvSpec` from the five pieces still in progress (the stops, the window, the next key, the
start of the loop and one iteration); every other piece is applied.
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- **`SweepEvSpec`** from the remaining pieces. -/
theorem sweepEvSpec_of_rest (hStop : StopTask) (hWin : WinTask) (hKey : KeyTask)
    (hL0 : LoopStartTask) (hL1 : StepTask) : SweepEvSpec :=
  sweepEvSpec_of asmTask initTask genTask hStop hWin orgsTask hKey prepTask hL0 hL1 doneTask
    regArcsTask countTask

end

end SweepEv

end Chazelle.Core
