/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The tile and the output string of each wanted position

Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T and is indexed by one output
string of T".  For the i-th wanted position (I, J) the routine wanted(w, L, Lo, N, K0, nB, aWI, aWJ,
band, dig3, mask, tid) writes the number BAND[I] · nB + BAND[J] of its tile to tid + i, the code
Spec.outCodeOfPos L m I J of its output string to tid + w + i, and the L digits of the code to
tid + 2 w + i L.  The code is formed by Horner's rule in base 10 while walking the mask of the
subset number BLOCK[I] · K₀ + BLOCK[J]: digit 9 at a level of the subset, and otherwise 3 x + y for
the next base-3 digits x, y of the offsets of I and J.  O(L) steps for each position.

In the paper's letters (Sections 2.3.3 and 2.3.4): D = 4^m, N₀ = 3^(L-m) is the side of a block,
K₀ = ⌊√binom(L, m)⌋ is the number of blocks along the side of a tile, and the offset of I is
I mod N₀, the place of I within its block.

A round of the loop over the positions has three parts, each with its lemma: `prepBlock_ends` (the
position, its tile and the three addresses), `levelLoop_ends` (the walk along the mask; one level is
`levelRound_ends`) and `finishBlock_ends` (the tile and the code are stored).  `wantedRound_ends`
puts them together, `wantedBody_ends` is the loop, and `wanted_entry` is the result for the callers:
a call of procedure `pWanted` does what `WantedSpec` says.
-/


namespace Light.Sec2.Wanted


/-! ## The program -/

namespace Local

/- The number w of wanted positions. -/
slots WW
/- The number L of levels. -/
slots 1 LL
/- Lo = L - m, the number of base-3 digits of an offset. -/
slots 2 LO
/- The size N. -/
slots 3 NN
/- K₀, the number of blocks along the side of a tile. -/
slots 4 KK
/- The number nB of bands. -/
slots 5 NB
/- The rows of the wanted positions. -/
slots 6 AWI
/- The columns of the wanted positions. -/
slots 7 AWJ
/- The table BAND, followed by the table BLOCK. -/
slots 8 BAND
/- The base-3 digits of the offsets. -/
slots 9 DIG3
/- The masks of the subsets. -/
slots 10 MASK
/- Where the numbers of the tiles, the codes and the digits are written. -/
slots 11 TID
/- The number i of the position. -/
slots 12 CI
/- The row I. -/
slots 13 PI
/- The column J. -/
slots 14 PJ
/- The address of the mask. -/
slots 15 AM
/- The address of the next digit of the offset of I. -/
slots 16 AI
/- The address of the next digit of the offset of J. -/
slots 17 AJ
/- The number formed so far. -/
slots 18 ACC
/- The level. -/
slots 19 LEV
/- The address of the row of digits. -/
slots 20 ROW
/- The digit. -/
slots 21 DIG
/- The number of the tile. -/
slots 22 TILE

end Local

open Local

/-- The digit is stored and appended to the number, and the level moves on. -/
def levelTail : Stmt :=
  .store (v ROW +' v LEV) (v DIG) ;;
  .set ACC (v ACC *' k 10 +' v DIG) ;;
  .set LEV (v LEV +' k 1)

/-- The digit of the level: 9 at a level of the subset, and otherwise 3 x + y for the next digits
x, y of the two offsets. -/
def levelDigit : Stmt :=
  .ite (M (v AM +' v LEV) <' k 1)
    (.set DIG (k 3 *' M (v AI) +' M (v AJ)) ;; .set AI (v AI +' k 1) ;; .set AJ (v AJ +' k 1))
    (.set DIG (k 9))

/-- One level of the walk along the mask. -/
def levelRound : Stmt :=
  levelDigit ;; levelTail

/-- The walk along the mask. -/
def levelLoop : Stmt :=
  .while (v LEV <' v LL) levelRound

/-- Before the walk: the position, the number of its tile, and the three addresses. -/
def prepBlock : Stmt :=
  .set PI (M (v AWI +' v CI)) ;; .set PJ (M (v AWJ +' v CI)) ;;
  .set TILE (M (v BAND +' v PI) *' v NB +' M (v BAND +' v PJ)) ;;
  .set AM (v MASK +' (M (v BAND +' v NN +' v PI) *' v KK +' M (v BAND +' v NN +' v PJ)) *' v LL) ;;
  .set AI (v DIG3 +' v PI *' v LO) ;; .set AJ (v DIG3 +' v PJ *' v LO) ;;
  .set ACC (k 0) ;; .set LEV (k 0)

/-- After the walk: the number of the tile and the code are stored, and the counters move on. -/
def finishBlock : Stmt :=
  .store (v TID +' v CI) (v TILE) ;;
  .store (v TID +' v WW +' v CI) (v ACC) ;;
  .set CI (v CI +' k 1) ;; .set ROW (v ROW +' v LL)

/-- wanted(w, L, Lo, N, K0, nB, aWI, aWJ, band, dig3, mask, tid). -/
def wantedBody : Stmt :=
  .set CI (k 0) ;; .set ROW (v TID +' v WW +' v WW) ;;
  .while (v CI <' v WW) (prepBlock ;; levelLoop ;; finishBlock)


/-! ## The walk along one mask -/

variable {i : ℕ}

/-! ## Before and after the walk -/


/-! ## One position -/

section Position

variable {w : ℕ}
  (hi : i < w)


include hi

end Position

end Light.Sec2.Wanted

namespace Light.Sec2


