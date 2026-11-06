/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The tries of all tiles

Proof of Theorem 30, "Preprocessing": "Finally, we compute the values of all the boxes of each of
the at most 4N²/M tiles". The routine `tile` builds the trie of a tile, and this routine calls it
for every tile. The tiles are taken in row-major order. Three pointers move along: the address of
the encoding of the row band, that of the column band, and the cell for the root of the tile. The
text has three parts, one inside the other: one tile (`allTilesStep`), one row of tiles
(`allTilesRow`), all rows (`allTilesBody`). The invariant `AllTiles.Inv` says what the memory holds
before the tile (β, β'); there is one lemma for each part.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/


/-- One tile, and on to the next column band. -/
def allTilesStep  :=
  .call 50 [v 14, v 15, v 13, v 5, v 6, v 7, v 8, v 9, v 10]
    16 ;;
  .set 13 (v 13 +' k 1) ;;
  .set 15 (v 15 +' v 3) ;;
  .set 12 (v 12 +' k 1)

/-- One row of tiles, and on to the first tile of the next row band. -/
def allTilesRow  :=
  .while (v 12 <' v 2) allTilesStep ;;
  .set 14 (v 14 +' v 3) ;;
  .set 11 (v 11 +' k 1) ;;
  .set 12 (k 0) ;;
  .set 15 (v 1)

/-- allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt). -/
def allTilesBody  :=
  .set 11 (k 0) ;;
  .set 12 (k 0) ;;
  .set 13 (v 4) ;;
  .set 14 (v 0) ;;
  .set 15 (v 1) ;;
  .set 16 (k 0) ;;
  .while (v 11 <' v 2) allTilesRow

namespace AllTiles

/-! ## The invariant and one tile -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : Light.Memory} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The tries and the roots of the tiles before the tile (β, β'). -/
def triesBefore (x : AllTilesArgs) β β' :=
  allTries x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')

/-- What the memory μ' holds before the tile (β, β'): the tries and the roots of the tiles before
it; nothing below cur or behind the trie area has changed since μ. -/
structure Mem (μ μ' : Light.Memory) (x : AllTilesArgs) (β β' : ℕ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp (triesBefore x β β').cells
  roots : SegN μ' x.aR (triesBefore x β β').roots
  same : SameOn x.Kept μ μ'

/-- The state before the tile (β, β'): the three pointers stand at this tile, and the memory is as
Mem says. -/
def Inv (μ : Light.Memory) (x : AllTilesArgs) (β β' : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : Light.Memory),
    σ = ⟨frame [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), β, β', (x.aR + (β * x.nB + β') : ℕ), (x.aENCA + β * 10 ^ x.L : ℕ),
      (x.aENCB + β' * 10 ^ x.L : ℕ), void], μ'⟩ ∧
    Mem μ μ' x β β'

/-- The arguments of the call of `tile` for the tile (β, β'), and the data behind them. -/
def tileArgs (x : AllTilesArgs) (β β' : ℕ) : TileArgs where
  L := x.L
  m := x.m
  t := x.t
  encA := x.encA β
  encB := x.encB β'
  aA := x.aENCA + β * 10 ^ x.L
  aB := x.aENCB + β' * 10 ^ x.L
  tr := x.tr
  cap := x.cap
  fp := x.fp
  cur := x.cur
  box := x.box
  aR := x.aR
  s := triesBefore x β β'
  old := storedAll x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  lo := 1

/-- Each tile before (β, β') has one root. -/
private theorem length_roots_triesBefore x β β' :
    (triesBefore x β β').roots.length = β * x.nB + β' := by
  rw [triesBefore, length_roots_allTries, length_tilesBefore]

/-- The tries after the tile (β, β'). -/
private theorem tries_tileArgs x β β' :
    (tileArgs x β β').tries = triesBefore x β (β' + 1) := by
  rw [triesBefore, tilesBefore_succ, allTries_snoc]
  rfl

/-! ## One row, and all rows -/

end AllTiles

end Light.Sec4
