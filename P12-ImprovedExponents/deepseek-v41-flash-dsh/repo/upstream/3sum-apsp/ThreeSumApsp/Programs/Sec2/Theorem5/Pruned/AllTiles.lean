/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

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

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## What the callers may assume

`RunTilesSpec` says what a call of procedure `pRunTiles` does, and in how many steps: a constant c
times a shape that depends on the sizes. -/

/-- The arguments of runTiles, with the data behind them.  EA β and EB β' are the encodings of the
bands, which stand at enca and encb, one behind the other; s t = START[t]; codes t are the codes of
tile t; w is the number of wanted positions; A and B bound the numbers in the encodings. -/
structure TilesArgs : Type where
  (nB L enca encb start sc sv sp p10 : ℕ)
  (w : ℕ) (EA EB : ℕ → List ℤ) (s : ℕ → ℕ) (codes : ℕ → List ℕ) (A B : ℤ)

/-- What runTiles assumes.  Everything that is read lies below SV; then come the w cells of SV and,
from sp on, the stack of the pruned recursion. -/
structure TilesPre (lim : Limits) (μ : ℕ → ℤ) (x : TilesArgs) : Prop where
  hp10 : Seg μ x.p10 (powList 10 (x.L + 1))
  hea : ∀ β < x.nB, Seg μ (x.enca + β * 10 ^ x.L) (x.EA β)
  heb : ∀ β < x.nB, Seg μ (x.encb + β * 10 ^ x.L) (x.EB β)
  lea : ∀ β < x.nB, (x.EA β).length = 10 ^ x.L
  leb : ∀ β < x.nB, (x.EB β).length = 10 ^ x.L
  hstart : ∀ t ≤ x.nB * x.nB, μ (x.start + t) = x.s t
  mono : ∀ t < x.nB * x.nB, x.s t ≤ x.s (t + 1)
  s_le : x.s (x.nB * x.nB) ≤ x.w
  hcodes : ∀ t < x.nB * x.nB, SegN μ (x.sc + x.s t) (x.codes t)
  lcodes : ∀ t < x.nB * x.nB, (x.codes t).length = x.s (t + 1) - x.s t
  sorted : ∀ t < x.nB * x.nB, (x.codes t).Pairwise (· < ·)
  small : ∀ t < x.nB * x.nB, ∀ c ∈ x.codes t, c < 10 ^ x.L
  boundA : ∀ β < x.nB, AbsLe (x.EA β) x.A
  boundB : ∀ β < x.nB, AbsLe (x.EB β) x.B
  room : 10 ^ x.L * (x.A * x.B) ≤ lim.word
  ten : ((10 ^ (x.L + 1) : ℕ) : ℤ) ≤ lim.word
  p10_le : x.p10 + (x.L + 1) ≤ x.sc := by light_arith
  enca_le : x.enca + x.nB * 10 ^ x.L ≤ x.sc := by light_arith
  encb_le : x.encb + x.nB * 10 ^ x.L ≤ x.sc := by light_arith
  start_le : x.start + (x.nB * x.nB + 1) ≤ x.sc := by light_arith
  sc_le : x.sc + x.w ≤ x.sv := by light_arith
  sv_le : x.sv + x.w ≤ x.sp := by light_arith
  sp_le : x.sp + x.L * (3 * x.w + 11) ≤ lim.space := by light_arith

/-! ## The program -/

namespace TilesLocal

/-- The number nB of bands. -/
abbrev NB : ℕ := 0
/-- The number L of levels. -/
abbrev LL : ℕ := 1
/-- T = 10^L, the length of an encoding. -/
abbrev TT : ℕ := 2
/-- The encoding of the row band β. -/
abbrev PEA : ℕ := 3
/-- The encodings of the column bands. -/
abbrev ENCB : ℕ := 4
/-- The address of START[t]. -/
abbrev PST : ℕ := 5
/-- The codes, sorted. -/
abbrev SC : ℕ := 6
/-- The values. -/
abbrev SV : ℕ := 7
/-- The stack of the pruned recursion. -/
abbrev SP : ℕ := 8
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 9
/-- The row band β. -/
abbrev CB : ℕ := 10
/-- The column band β'. -/
abbrev CC : ℕ := 11
/-- The encoding of the column band β'. -/
abbrev PEB : ℕ := 12
/-- START[t]. -/
abbrev S0 : ℕ := 13
/-- START[t + 1]. -/
abbrev S1 : ℕ := 14
/-- A result that is not used. -/
abbrev RES : ℕ := 15

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

variable {lim : Limits} {x : TilesArgs} {μ μ' : ℕ → ℤ} {β i : ℕ}

namespace TilesPre

end TilesPre

/-- The arguments of the call of pruned for the tile (β, i). -/
@[simp]
def TilesArgs.tile (x : TilesArgs) (β i : ℕ) : PrunedArgs where
  aEA := x.enca + β * 10 ^ x.L
  aEB := x.encb + i * 10 ^ x.L
  base := 0
  l := x.sc + x.s (β * x.nB + i)
  out := x.sv + x.s (β * x.nB + i)
  sp := x.sp
  p10 := x.p10
  Lmax := x.L
  EA := x.EA β
  EB := x.EB i
  codes := x.codes (β * x.nB + i)
  A := x.A
  B := x.B

section Tile

variable (pre : TilesPre lim μ x) (hβ : β < x.nB) (hi : i < x.nB)
include pre hβ hi

end Tile

/-! ## One tile -/

variable {P : Program} {c e : ℕ}

/-! ## The two loops -/

end Light.Sec2
