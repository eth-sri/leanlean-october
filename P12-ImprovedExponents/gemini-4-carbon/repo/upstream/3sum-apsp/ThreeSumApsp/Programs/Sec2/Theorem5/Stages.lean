/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.AllTiles
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Report
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.SortedFacts
public import ThreeSumApsp.Programs.Tasks

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

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

open ThreeSumApsp.Spec

/-! ## The local variables and the cells of the directory -/

namespace Solver

/-- Local 10 of the solver: m. -/
abbrev Expo : ℕ := 10
/-- Local 11 of the solver: a power of four. -/
abbrev Pow4 : ℕ := 11
/-- Local 12 of the solver: L = 19 m. -/
abbrev Levels : ℕ := 12
/-- Local 13 of the solver: takes the results of the calls. -/
abbrev Void : ℕ := 13
/-- Local 14 of the solver: the address of TID. -/
abbrev AdrTid : ℕ := 14
/-- Local 16 of the solver: the number of bands. -/
abbrev Bands : ℕ := 16
/-- Local 22 of the solver: the address of PERM. -/
abbrev AdrPerm : ℕ := 22
/-- Local 23 of the solver: the number of tiles. -/
abbrev Tiles : ℕ := 23
/-- Local 26 of the solver: the address of SC. -/
abbrev AdrSc : ℕ := 26

/-- Cell 4 of the directory: L - m. -/
abbrev DirOuter : ℕ := 4
/-- Cell 7 of the directory: K₀. -/
abbrev DirRoot : ℕ := 7
/-- Cell 9 of the directory: the number of bands. -/
abbrev DirBands : ℕ := 9
/-- Cell 10 of the directory: 10^L. -/
abbrev DirLeaves : ℕ := 10
/-- Cell 17 of the directory: the address of the powers of ten. -/
abbrev DirP10 : ℕ := 17
/-- Cell 21 of the directory: the address of the table of subsets. -/
abbrev DirMask : ℕ := 21
/-- Cell 22 of the directory: the address of the bands of the rows. -/
abbrev DirBand : ℕ := 22
/-- Cell 24 of the directory: the address of the base-3 digits. -/
abbrev DirDig3 : ℕ := 24
/-- Cell 26 of the directory: the address of the encodings of the row bands. -/
abbrev DirEncA : ℕ := 26
/-- Cell 27 of the directory: the address of the encodings of the column bands. -/
abbrev DirEncB : ℕ := 27
/-- Cell 30 of the directory: the end of the shared block. -/
abbrev DirEnd : ℕ := 30

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

variable {lim : Limits} {P : Program} {c d : ℕ} {p : Par} {hmL : p.m ≤ p.L}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {w : ℕ}
  {u e1 e11 : ℤ} {ax ay wi wj out fr : ℕ} {A : ℤ} {I J : ℕ → ℕ} {V : ℕ → ℤ} {μ : ℕ → ℤ}

/-! ## The report -/

/-! ## The pruned recursions -/

/-! ## The codes in sorted order -/

/-! ## The sort -/

/-! ## Tiles, codes and digits of the wanted positions -/

/-! ## The shared stage -/

end Light.Sec2
