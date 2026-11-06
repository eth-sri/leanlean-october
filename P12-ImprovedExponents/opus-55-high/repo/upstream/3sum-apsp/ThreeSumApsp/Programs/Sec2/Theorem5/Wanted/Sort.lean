/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.RadixPass
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
import Mathlib.Tactic.Linarith

/-!
# Theorem 5 in the light language: sorting the wanted positions

sortWanted(w, L, nT, tid, dgt, perm): "sort the sets W_T" (Section 2.4.4), by a radix sort of the
indices 0, …, w - 1, in O((L + 1) (w + 10) + nT) steps.  The routine writes the list 0, …, w - 1 to
perm (swInit_ends).  Then, unless w = 0, it makes L stable passes on the stored digits of the codes,
the last digit first: after r of them the list is sorted by the last r digits (swDigit_ends for one
pass, swDigits_ends for all).  One more pass, on the numbers of the tiles, sorts the list by tile
and code and leaves the number of positions in the tiles below s, for every s (swTiles_ends).
sortWantedBody_ends puts the parts together, and sortWanted_entry is the specification
SortWantedSpec that the callers use.
-/



namespace Light.Sec2

/-! ## The program -/

namespace SortWanted

/- The local variables of sortWanted: the arguments w (Num), L (Levels), nT (Tiles), tid (TileOf),
dgt (Digits), perm (Perm); a counter (Idx); the unused results of the calls (Res).  A pass
(radixPass) reads w and perm from the locals 0 and 5 and writes to local 7, which are Num, Perm and
Res. -/
slots Num Levels Tiles TileOf Digits Perm Idx Res

end SortWanted

open SortWanted

/-- perm[i] := i for i < w. -/
def swInit : Stmt := .for Idx (v Num) (.store (v Perm +' v Idx) (v Idx))

/-- The pass on the digit whose index is in the counter. -/
def swDigit : Stmt :=
  radixPass pCountSort pCopy (v Digits) (v Levels) (v Idx) (k 10) (v Perm +' v Num +' v Num)

/-- The passes on the digits L - 1, …, 0. -/
def swDigits : Stmt :=
  .set Idx (v Levels) ;;
  .while (k 0 <' v Idx) (.set Idx (v Idx -' k 1) ;; swDigit)

/-- The pass on the numbers of the tiles. -/
def swTiles : Stmt :=
  radixPass pCountSort pCopy (v TileOf) (k 1) (k 0) (v Tiles)
    (v Perm +' v Num +' v Num +' v Tiles +' k 11)

/-- sortWanted(w, L, nT, tid, dgt, perm).  For w = 0 there are no passes on the digits: only for
w > 0 do the assumptions say that L fits in a word. -/
def sortWantedBody : Stmt := swInit ;; .ite (k 0 <' v Num) swDigits .skip ;; swTiles

/-! ## What is assumed, and the state between the passes -/

namespace SortWanted

end SortWanted

/-! ## The list 0, …, w - 1 -/

/-! ## The passes on the digits -/

/-! ## The pass on the tiles -/

/-! ## The routine -/
