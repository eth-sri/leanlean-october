module

public import Chazelle.Core.SweepEvStepL1
public import Chazelle.Core.SweepEvDone3

/-!
# The sweep (WP-D), stage 3: Task L2 (the last iteration)

`doneNoCut : DoneNoCut` (from `no_cut_done`), hence **`doneTask : DoneTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- **No cut after the last key.** -/
theorem doneNoCut : DoneNoCut := by
  intro sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E hL hIt hd
  exact no_cut_done E hL hIt hd

/-- **Task L2: the last iteration.** -/
theorem doneTask : DoneTask := doneTask_of doneNoCut

end

end SweepEv

end Chazelle.Core
