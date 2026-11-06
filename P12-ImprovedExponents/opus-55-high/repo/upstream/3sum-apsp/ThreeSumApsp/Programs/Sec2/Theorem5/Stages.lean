/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.AllTiles
import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Report
import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.SortedFacts
import ThreeSumApsp.Programs.Tasks

/-!
# Theorem 5: the solver, stage by stage

The text of the solver after the search for m ("The algorithm", Section 2.4.4), cut into six parts:
the shared stage; tiles, codes and digits of the wanted positions (the code of a position is its
output string, read as a number); the sort; the codes in sorted order; the pruned recursions; the
report. There is one lemma for each part together with everything that follows it (fromShared_ends
to reportCall_ends), so that each lemma ends with the lemma of the next part. The lemmas are stated
for arbitrary parameters p, matrices X, Y and positions (I i, J i) (WantedJob). The result is
fromShared_ends: from the state after the search for m the solver ends within timeFromShared steps,
with the entries of XY at the w wanted positions in the cells from out on, and nothing else below
the free pointer changed (Reported).

Every stage writes above everything that the stages before it have written, except the report, which
writes the output. So each lemma hands on what the earlier stages have left, in a memory that agrees
with the earlier one below the area just written.
-/



namespace Light.Sec2


/-! ## The local variables and the cells of the directory -/

namespace Solver

/- Local 10 of the solver: m. -/
slots 10 Expo
/- Local 11 of the solver: a power of four. -/
slots 11 Pow4
/- Local 12 of the solver: L = 19 m. -/
slots 12 Levels
/- Local 13 of the solver: takes the results of the calls. -/
slots 13 Void
/- Local 14 of the solver: the address of TID. -/
slots 14 AdrTid
/- Local 16 of the solver: the number of bands. -/
slots 16 Bands
/- Local 22 of the solver: the address of PERM. -/
slots 22 AdrPerm
/- Local 23 of the solver: the number of tiles. -/
slots 23 Tiles
/- Local 26 of the solver: the address of SC. -/
slots 26 AdrSc

/- Cell 4 of the directory: L - m. -/
slots 4 DirOuter
/- Cell 7 of the directory: K₀. -/
slots 7 DirRoot
/- Cell 9 of the directory: the number of bands. -/
slots 9 DirBands
/- Cell 10 of the directory: 10^L. -/
slots 10 DirLeaves
/- Cell 17 of the directory: the address of the powers of ten. -/
slots 17 DirP10
/- Cell 21 of the directory: the address of the table of subsets. -/
slots 21 DirMask
/- Cell 22 of the directory: the address of the bands of the rows. -/
slots 22 DirBand
/- Cell 24 of the directory: the address of the base-3 digits. -/
slots 24 DirDig3
/- Cell 26 of the directory: the address of the encodings of the row bands. -/
slots 26 DirEncA
/- Cell 27 of the directory: the address of the encodings of the column bands. -/
slots 27 DirEncB
/- Cell 30 of the directory: the end of the shared block. -/
slots 30 DirEnd

end Solver

open ThinArg Solver

/-! ## The text -/

/-- The report. -/
def reportCall : Stmt :=
  .call pReport [v Wanted, v AdrPerm, v AdrSc +' v Wanted, v AdrOut] Void

/-- The pruned recursions, and what follows. -/
def fromTiles : Stmt :=
  .call pRunTiles [v Bands, v Levels, M (v Free +' k DirLeaves), M (v Free +' k DirEncA),
    M (v Free +' k DirEncB), v AdrPerm +' v Wanted +' v Wanted +' v Tiles +' k 11, v AdrSc,
    v AdrSc +' v Wanted, v AdrSc +' v Wanted +' v Wanted, M (v Free +' k DirP10)] Void ;;
  reportCall

/-- The codes in sorted order, and what follows. -/
def fromGather : Stmt :=
  .set AdrSc (v AdrPerm +' v Wanted +' v Wanted +' v Tiles +' k 11 +' v Tiles +' k 1) ;;
  .call pGather [v Wanted, v AdrPerm, v AdrTid +' v Wanted, v AdrSc] Void ;;
  fromTiles

/-- The sort, and what follows. -/
def fromSort : Stmt :=
  .set AdrPerm (v AdrTid +' v Wanted +' v Wanted +' v Wanted *' v Levels) ;;
  .set Tiles (v Bands *' v Bands) ;;
  .call pSortWanted [v Wanted, v Levels, v Tiles, v AdrTid, v AdrTid +' v Wanted +' v Wanted,
    v AdrPerm] Void ;;
  fromGather

/-- Tiles, codes and digits of the wanted positions, and what follows. -/
def fromWanted : Stmt :=
  .set AdrTid (M (v Free +' k DirEnd)) ;;
  .set Bands (M (v Free +' k DirBands)) ;;
  .call pWanted [v Wanted, v Levels, M (v Free +' k DirOuter), v Rows, M (v Free +' k DirRoot),
    v Bands, v AdrWI, v AdrWJ, M (v Free +' k DirBand), M (v Free +' k DirDig3),
    M (v Free +' k DirMask), v AdrTid] Void ;;
  fromSort

/-- The shared stage, and what follows. -/
def fromShared : Stmt :=
  .set Levels (k 19 *' v Expo) ;;
  .call pShared [v Levels, v Expo, v Rows, v Cols, v AdrX, v AdrY, v Free] Void ;;
  fromWanted

/-! ## The times: each stage with everything that follows it -/

/-! ## The report -/

/-! ## The pruned recursions -/

/-! ## The codes in sorted order -/

/-! ## The sort -/

/-! ## Tiles, codes and digits of the wanted positions -/

/-! ## The shared stage -/
