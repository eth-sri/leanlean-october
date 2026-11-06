/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Cutting an increasing list of codes into its ten slices (step (2) of Pruned, Section 2.4.2)

segBounds goes once through an increasing list of codes of n + 1 digits.  The codes with first digit
z are consecutive; it notes where they start, and writes every code without its first digit.

* The list.  `SegInv` says where the pass stands: i codes are copied, z is the current first digit,
  and lo = z 10^n.  A code below lo + 10^n is copied (`SegInv.copy`); otherwise the pass goes on to
  the next first digit (`SegInv.advance`), and the position reached is the start of the next slice
  (`SegInv.segStart_succ`).
* The memory.  `SegMem` says what has been written, `SegMem.copy` and `SegMem.advance` what a round
  adds, and `SegMem.slices` that in the end the ten slices stand in the memory.
* The program.  `segCopy_ends` and `segAdvance_ends` treat the two kinds of rounds, and
  `segBounds_entry` the loop.  The result: a call takes at most `cSegBounds` steps for each code and
  each of the eleven bounds; afterwards the cells bnd to bnd + 10 hold the starts of the slices, the
  slice at z stands at bnd + 11 + segStart n codes z, and no other cell has changed.
-/


namespace Light.Sec2


/-! ## The program -/

namespace SegLocal

/- The list of the codes. -/
slots PL
/- The length of the list. -/
slots 1 LEN
/- 10^n. -/
slots 2 PW
/- Where the bounds are written; the codes without first digits follow 11 cells later. -/
slots 3 BND
/- The position i in the list. -/
slots 4 CI
/- The first digit z. -/
slots 5 CZ
/- z 10^n. -/
slots 6 LO
/- (z + 1) 10^n. -/
slots 7 HI

end SegLocal

open SegLocal

/-- The code at position i has first digit z: it is written without that digit. -/
def segCopy : Stmt :=
  .store (v BND +' k 11 +' v CI) (M (v PL +' v CI) -' v LO) ;; .set CI (v CI +' k 1)

/-- The next first digit: z := z + 1, the position reached is noted at bnd + z, and the two
thresholds move up. -/
def segAdvance : Stmt :=
  .set CZ (v CZ +' k 1) ;;
  .store (v BND +' v CZ) (v CI) ;;
  .set LO (v HI) ;;
  .set HI (v HI +' v PW)

/-- segBounds(l, len, pw, bnd). -/
def segBoundsBody : Stmt :=
  .set CI (k 0) ;;
  .set CZ (k 0) ;;
  .set LO (k 0) ;;
  .set HI (v PW) ;;
  .store (v BND) (k 0) ;;
  .while (v CZ <' k 10) (
    .ite (v CI <' v LEN)
      (.ite (M (v PL +' v CI) <' v HI) segCopy segAdvance)
      segAdvance)

/-! ## The list -/

/-! ## The memory -/

/-! ## The pass -/

