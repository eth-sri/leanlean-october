/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Memory

/-!
# The pruned recursion (Section 2.4.2), recursive as printed

pruned(n, ea, eb, l, len, out, sp, p10).  The set S passed to the call is the increasing list of len
codes at l; ea and eb are the addresses at which the parts of the two encodings below the current
vertex begin; the array that is returned is written to the len cells from out, in the order of the
list.  The frame of a call with n ≥ 1 starts at sp: 11 cells for the bounds of the ten slices, len
cells for the codes without their first digits, len cells for the list of a child, len cells for the
values of a child.

(1) If n = 0: the product of the two numbers looked up, for each code of the list
    (`prunedBody_ends_zero`).
(2) The slices S_z are segments of the list (segBounds); S_λ is the merge of the slice at z_ij and
    the slice at z₀ (`prunedSlice_ends`, then union).
(3) For each term λ with S_λ ≠ ∅: the recursive call.
(4) The slice of the result at z_ij is C_{P_ij} restricted to S_{z_ij} (pick, writing); the slice at
    z₀ is the sum of the ten C_λ restricted to S_{z₀} (pick, adding, after the cells have been
    cleared).  Steps (3) and (4) for one term are `prunedChild_ends`.

One round of the loop over the ten terms is `prunedRound_ends`; the case n ≥ 1 is
`prunedSetup_ends` followed by the loop (`prunedBody_ends_succ`); `PrunedCtx.entry` is the induction
on n.  What the calls do to the memory is proved in Pruned/Memory.lean; here each call is one step.
-/


namespace Light.Sec2


/-! ## The program -/

namespace PrunedLocal

/- The number n of levels that are left. -/
slots NN
/- Where the part of the first encoding below the current vertex begins. -/
slots 1 PA
/- Where the part of the second encoding below the current vertex begins. -/
slots 2 PB
/- The list of the codes that are passed to the call. -/
slots 3 PL
/- The length of that list. -/
slots 4 LEN
/- Where the values are written. -/
slots 5 OUT
/- The frame of the call; it begins with the bounds of the ten slices. -/
slots 6 SP
/- The table of the powers of ten. -/
slots 7 P10
/- 10^(n-1); for n = 0 the product of the two numbers looked up. -/
slots 8 PW
/- Results of calls that are not used. -/
slots 9 RES
/- The codes without their first digits. -/
slots 10 COD
/- The list of the child. -/
slots 11 CH
/- The values of the child. -/
slots 12 VAL
/- The frame of the child. -/
slots 13 NXT
/- The position of the slice at z₀. -/
slots 14 Z0
/- The length of the slice at z₀. -/
slots 15 NZ0
/- The term λ. -/
slots 16 LAM
/- The position of the slice at the output variable of λ. -/
slots 17 POS
/- The length of that slice (0 for λ = P₀). -/
slots 18 NPOS
/- The length of the list of the child. -/
slots 19 NCH

end PrunedLocal

open PrunedLocal

/-- Step (2), first half: the position and the length of the slice at the output variable of λ. -/
def prunedSlice : Stmt :=
  .set POS (M (v SP +' v LAM)) ;;
  .ite (v LAM <' k 9) (.set NPOS (M (v SP +' v LAM +' k 1) -' v POS)) (.set NPOS (k 0))

/-- Steps (3) and (4) for a term λ with S_λ ≠ ∅. -/
def prunedChild : Stmt :=
  .call pPruned [v NN -' k 1, v PA +' v LAM *' v PW, v PB +' v LAM *' v PW, v CH, v NCH, v VAL,
    v NXT, v P10] RES ;;
  .call pPick [v COD +' v POS, v NPOS, v CH, v NCH, v VAL, v OUT +' v POS, k 0] RES ;;
  .call pPick [v COD +' v Z0, v NZ0, v CH, v NCH, v VAL, v OUT +' v Z0, k 1] RES

/-- One round of the loop over the ten terms. -/
def prunedRound : Stmt :=
  prunedSlice ;;
  .call pUnion [v COD +' v POS, v NPOS, v COD +' v Z0, v NZ0, v CH] NCH ;;
  .ite (k 0 <' v NCH) prunedChild .skip ;;
  .set LAM (v LAM +' k 1)

/-- What a call with n ≥ 1 does before the loop: the slices are found, the parts of the frame get
their addresses, and the cells of the slice at z₀ are cleared. -/
def prunedSetup : Stmt :=
  .set PW (M (v P10 +' (v NN -' k 1))) ;;
  .call pSegBounds [v PL, v LEN, v PW, v SP] RES ;;
  .set COD (v SP +' k 11) ;;
  .set CH (v COD +' v LEN) ;;
  .set VAL (v CH +' v LEN) ;;
  .set NXT (v VAL +' v LEN) ;;
  .set Z0 (M (v SP +' k 9)) ;;
  .set NZ0 (v LEN -' v Z0) ;;
  .call pFill [v OUT +' v Z0, v NZ0, k 0] RES ;;
  .set LAM (k 0)

/-- pruned(n, ea, eb, l, len, out, sp, p10). -/
def prunedBody : Stmt :=
  .ite (v NN =' k 0)
    (.set PW (M (v PA) *' M (v PB)) ;;
     .call pFill [v OUT, v LEN, v PW] RES)
    (prunedSetup ;;
     .while (v LAM <' k 10) prunedRound)

/-! ## What the proofs assume -/

/-! ## Step (1) -/

/-! ## One round of the loop -/

/-! ## The case n ≥ 1 -/

/-! ## The recursion -/
