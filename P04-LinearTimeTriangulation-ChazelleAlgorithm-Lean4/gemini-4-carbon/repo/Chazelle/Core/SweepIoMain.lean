module

public import Chazelle.Core.SweepIoQry
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepIoAsm5
public import Chazelle.Core.SweepIoTopCount

/-!
# The sweep RAM (WP-D): `SweepSpecH` from stages 2/3 and the candidate steps

`sweepSpecH_of`: the per-query procedure (`qry_of_cands`, from the candidate steps of the two
sides `Cand0Spec`, `Cand1Spec`), the query loop (`loopSpec_of`, with `topCount`) and the assembly
(`asmGoal`, with stages 2/3 `SweepEvSpec`) give `SweepSpecH`.
-/

namespace Chazelle.Core

namespace SweepIo

@[expose] public section

/-- **WP-D: the sweep with height-coded queries**, from stages 2/3 and the candidate steps. -/
theorem sweepSpecH_of (hE : SweepEvSpec) (h0 : Cand0Spec) (h1 : Cand1Spec) : SweepSpecH := by
  obtain ⟨init0, Aux, κ0, hInit, hQ⟩ := qry_of_cands h0 h1
  exact asmGoal hE init0 Aux κ0 hInit (loopSpec_of hQ topCount)

end

end SweepIo

end Chazelle.Core
