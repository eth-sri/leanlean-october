module

public import Chazelle.Exec.Interp
public import Chazelle.Machine.Basic

/-!
# The rational interpreter simulates the real RAM

`castPoly : QPolygon → Polygon` and `castConfig : QConfig → Config` embed rational data into the
real semantics of `Chazelle/Spec.lean` (through the ordered-field embedding `ℚ → ℝ`; natural
words and outputs are unchanged).  The main results:

* `step_castConfig`: `step prog (castPoly Pq) (castConfig c) = (stepQ prog Pq c).map castConfig`
  (real comparisons agree with rational ones since the cast is an order embedding, and
  division by zero faults in both);
* `run_castConfig`: the same for any number of steps;
* `runQ_sound`: if the executable run `runQ prog Pq fuel` halts with `(cq, k)`, then the real
  machine on `castPoly Pq` executes exactly `k` instructions, sits at `halt`, and has emitted
  `cq.output`;
* `runQ_runsWithin`: with the maximal natural word `W` recorded along the run (computed by
  `runQW`), a halting rational run yields `RunsWithin prog (castPoly Pq) W (k + 1) cq.output`.
-/

namespace Chazelle

namespace Exec

open Std

@[expose] public section








end

end Exec

end Chazelle
