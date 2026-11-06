/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

/-!
# Theorem 5 as a program: the pruned recursion on every tile

Section 2.4.4: "for each tile T with W_T ≠ ∅, we run Pruned(W_T)".

The wanted positions have been sorted by tile and, within a tile, by code.  The codes of the tile
number t = β nB + β' are the cells START[t], …, START[t+1] - 1 of SC.  runTiles walks over all
tiles; for each tile with START[t] < START[t+1] it calls the pruned recursion on the encodings of
the row band β and of the column band β', and the values land in the same cells of SV.

* The memory.  `TilesInv` says which tiles are done.  What the call for a tile assumes holds
  (`TilesPre.tile`), and the call finishes the tile (`TilesInv.of_call`); a tile without wanted
  positions is finished as it is (`TilesInv.of_empty`).
* The program.  `runTile_ends` treats one tile, `runTilesInner_ends` the tiles of a row band,
  `runBand_ends` a row band, and `runTiles_entry` all of them.
-/


namespace Light.Sec2


/-! ## What the callers may assume

`RunTilesSpec` says what a call of procedure `pRunTiles` does, and in how many steps: a constant c
times a shape that depends on the sizes. -/

/-- The arguments of runTiles, with the data behind them.  EA β and EB β' are the encodings of the
bands, which stand at enca and encb, one behind the other; s t = START[t]; codes t are the codes of
tile t; w is the number of wanted positions; A and B bound the numbers in the encodings. -/
structure TilesArgs : Type where
  (nB L enca encb start sc sv sp p10 : ℕ)
  (w : ℕ) (EA EB : ℕ → List ℤ) (s : ℕ → ℕ) (codes : ℕ → List ℕ) (A B : ℤ)


/-! ## The program -/

namespace TilesLocal

/- The number nB of bands. -/
slots NB
/- The number L of levels. -/
slots 1 LL
/- T = 10^L, the length of an encoding. -/
slots 2 TT
/- The encoding of the row band β. -/
slots 3 PEA
/- The encodings of the column bands. -/
slots 4 ENCB
/- The address of START[t]. -/
slots 5 PST
/- The codes, sorted. -/
slots 6 SC
/- The values. -/
slots 7 SV
/- The stack of the pruned recursion. -/
slots 8 SP
/- The table of the powers of ten. -/
slots 9 P10
/- The row band β. -/
slots 10 CB
/- The column band β'. -/
slots 11 CC
/- The encoding of the column band β'. -/
slots 12 PEB
/- START[t]. -/
slots 13 S0
/- START[t + 1]. -/
slots 14 S1
/- A result that is not used. -/
slots 15 RES

end TilesLocal

open TilesLocal

/-- One tile: the pruned recursion is called if the tile has wanted positions; then the column band,
its encoding and the address of START[t] move on. -/
def runTile : Stmt :=
  .set S0 (M (v PST)) ;; .set S1 (M (v PST +' k 1)) ;;
  .ite (v S0 <' v S1)
    (.call pPruned [v LL, v PEA, v PEB, v SC +' v S0, v S1 -' v S0, v SV +' v S0, v SP, v P10] RES)
    .skip ;;
  .set CC (v CC +' k 1) ;; .set PEB (v PEB +' v TT) ;; .set PST (v PST +' k 1)

/-- The tiles of one row band. -/
def runTilesInner : Stmt :=
  .while (v CC <' v NB) runTile

/-- One row band. -/
def runBand : Stmt :=
  .set CC (k 0) ;; .set PEB (v ENCB) ;; runTilesInner ;; .set CB (v CB +' k 1) ;;
  .set PEA (v PEA +' v TT)

/-- runTiles(nB, L, T, enca, encb, start, sc, sv, sp, p10). -/
def runTilesBody : Stmt :=
  .set CB (k 0) ;;
  .while (v CB <' v NB) runBand

/-! ## The memory -/

variable {x : TilesArgs} {β i : ℕ}

namespace TilesPre

end TilesPre

/-- The arguments of the call of pruned for the tile (β, i). -/
@[simp]
def TilesArgs.tile (x : TilesArgs) (β i : ℕ) : PrunedArgs := ⟨x.enca + β * 10 ^ x.L, x.encb + i * 10 ^ x.L, 0, x.sc + x.s (β * x.nB + i), x.sv + x.s (β * x.nB + i), x.sp, x.p10, x.L, x.EA β, x.EB i, x.codes (β * x.nB + i), x.A, x.B⟩

section Tile

variable (hβ : β < x.nB) (hi : i < x.nB)
include hβ hi

end Tile

/-! ## One tile -/

/-! ## The two loops -/
