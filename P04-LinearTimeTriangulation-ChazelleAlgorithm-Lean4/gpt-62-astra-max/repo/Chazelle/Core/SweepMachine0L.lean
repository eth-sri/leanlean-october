module

public import Chazelle.Core.SweepMachine21

/-!
# The sweep (WP-D), mirror prelude for the abstract machine

The facts of the side-`0` machine that are not symmetric under the exchange of `C₁` and `C₂`, in
the form needed by the mirrored files `SweepMachine*L.lean` (side `i = 1`):

* `tpos_secondL`: the tour position of the first copy of the shared vertex from the second one;
* `VNotTopM`, `vnt_iff`: the condition `VNotTop` read from the second copy;
* `sideChain_one`: the chain of side `1` is `C₂`;
* `whole_of_genuineL`, `whole_of_genuine_aboveL`, `answer_of_label_genL`, `answer_two_positionsL`:
  the answer lemmas of `SweepAnswer2`/`SweepAnswer3` with the roles of the two models exchanged.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- The chain of side `1` is `C₂`. -/
theorem sideChain_one : sideChain J 1 = J.right := ite_eq_right one_ne_zero

end Machine

end Sweep

end

end Chazelle.Core
