/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Restricting an array on a set of codes to a subset (step (4) of Pruned, Section 2.4.2)

pick walks once through an increasing list of codes (big), which has a value for each of its codes,
and through an increasing list of some of these codes (small).  It writes the values of the codes of
the second list, or adds them to what is there.

* The lists.  `PickInv` says where the walk stands.  If the two heads agree, the value is taken and
  both lists advance (`PickInv.hit`); if not, the head of the large list is skipped
  (`PickInv.miss`).
* The memory.  `PickMem` says which cells of the destination are finished; `PickMem.write` finishes
  one more.
* The program.  `pickTake_ends` treats the round in which a value is taken, `pickBody_ends` the
  loop, for both modes.  `pickSet_entry` and `pickAdd_entry` are the results for the callers: a call
  of procedure `pPick` does what `PickSetSpec` (writing) or `PickAddSpec` (adding) says, in at most
  `cPick` steps for each entry of the two lists.
-/


namespace Light.Sec2


/-! ## The program -/

namespace PickLocal

/- The small list. -/
slots PSUB
/- The length of the small list. -/
slots 1 NSUB
/- The large list. -/
slots 2 PU
/- The values of the codes of the large list. -/
slots 4 PVAL
/- The destination. -/
slots 5 PDST
/- The mode: 0 for writing, otherwise adding. -/
slots 6 ADD
/- The position i in the small list. -/
slots 7 CI
/- The position j in the large list. -/
slots 8 CJ

end PickLocal

open PickLocal

/-- The two heads agree: the value is written or added, and both lists advance. -/
def pickTake : Stmt :=
  .ite (v ADD =' k 0)
    (.store (v PDST +' v CI) (M (v PVAL +' v CJ)))
    (.store (v PDST +' v CI) (M (v PDST +' v CI) +' M (v PVAL +' v CJ))) ;;
  .set CI (v CI +' k 1) ;;
  .set CJ (v CJ +' k 1)

/-- pick(pSub, nSub, pU, nU, pVal, pDst, add).  The length nU of the large list, local 3, is not
read: the large list cannot end before the small one. -/
def pickBody : Stmt :=
  .set CI (k 0) ;;
  .set CJ (k 0) ;;
  .while (v CI <' v NSUB) (
    .ite (M (v PU +' v CJ) =' M (v PSUB +' v CI)) pickTake (.set CJ (v CJ +' k 1)))

/-! ## The lists -/

section Lists

end Lists

/-! ## The memory -/

/-! ## The walk -/

/-! ## The two results for the callers -/
