/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

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

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The program -/

namespace PickLocal

/-- The small list. -/
abbrev PSUB : ℕ := 0
/-- The length of the small list. -/
abbrev NSUB : ℕ := 1
/-- The large list. -/
abbrev PU : ℕ := 2
/-- The values of the codes of the large list. -/
abbrev PVAL : ℕ := 4
/-- The destination. -/
abbrev PDST : ℕ := 5
/-- The mode: 0 for writing, otherwise adding. -/
abbrev ADD : ℕ := 6
/-- The position i in the small list. -/
abbrev CI : ℕ := 7
/-- The position j in the large list. -/
abbrev CJ : ℕ := 8

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

/-! ## The memory -/


/-! ## The walk -/

/-! ## The two results for the callers -/

end Light.Sec2
