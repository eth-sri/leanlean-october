/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

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


namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace AllTiles

/- The local variables of `allTiles`: the arguments aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L,
mt; the row band β, the column band β', the cell for the root of the tile, the address of the
encoding of the row band, that of the column band, and a local for a result that is not used. -/
slots EncA EncB Bands Leaves RootTab Tries Free Cur Box Levels Last RowBand ColBand RootPtr RowEnc ColEnc Void

end AllTiles

open AllTiles in
/-- One tile, and on to the next column band. -/
def allTilesStep : Stmt :=
  .call Proc.tile [v RowEnc, v ColEnc, v RootPtr, v Tries, v Free, v Cur, v Box, v Levels, v Last]
    Void ;;
  .set RootPtr (v RootPtr +' k 1) ;;
  .set ColEnc (v ColEnc +' v Leaves) ;;
  .set ColBand (v ColBand +' k 1)

open AllTiles in
/-- One row of tiles, and on to the first tile of the next row band. -/
def allTilesRow : Stmt :=
  .while (v ColBand <' v Bands) allTilesStep ;;
  .set RowEnc (v RowEnc +' v Leaves) ;;
  .set RowBand (v RowBand +' k 1) ;;
  .set ColBand (k 0) ;;
  .set ColEnc (v EncB)

open AllTiles in
/-- allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt). -/
def allTilesBody : Stmt :=
  .set RowBand (k 0) ;;
  .set ColBand (k 0) ;;
  .set RootPtr (v RootTab) ;;
  .set RowEnc (v EncA) ;;
  .set ColEnc (v EncB) ;;
  .set Void (k 0) ;;
  .while (v RowBand <' v Bands) allTilesRow

namespace AllTiles

/-! ## The invariant and one tile -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The tries and the roots of the tiles before the tile (β, β'). -/
def triesBefore (x : AllTilesArgs) (β β' : ℕ) : TrieStore :=
  allTries x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')

/-- What the memory μ' holds before the tile (β, β'): the tries and the roots of the tiles before
it; nothing below cur or behind the trie area has changed since μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp (triesBefore x β β').cells
  roots : SegN μ' x.aR (triesBefore x β β').roots
  same : SameOn x.Kept μ μ'

/-- The state before the tile (β, β'): the three pointers stand at this tile, and the memory is as
Mem says. -/
def Inv (μ : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), β, β', (x.aR + (β * x.nB + β') : ℕ), (x.aENCA + β * 10 ^ x.L : ℕ),
      (x.aENCB + β' * 10 ^ x.L : ℕ), void], μ'⟩ ∧
    Mem μ μ' x β β'

/-- The arguments of the call of `tile` for the tile (β, β'), and the data behind them. -/
def tileArgs (x : AllTilesArgs) (β β' : ℕ) : TileArgs := ⟨x.L, x.m, x.t, x.encA β, x.encB β', x.aENCA + β * 10 ^ x.L, x.aENCB + β' * 10 ^ x.L, x.tr, x.cap, x.fp, x.cur, x.box, x.aR, triesBefore x β β', storedAll x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β'), 1⟩


/-- Each tile before (β, β') has one root. -/
theorem length_roots_triesBefore (x : AllTilesArgs) (β β' : ℕ) :
    (triesBefore x β β').roots.length = β * x.nB + β' := by
  rw [triesBefore, length_roots_allTries, length_tilesBefore]

variable {μ' : ℕ → ℤ}


/-- The tries after the tile (β, β'). -/
theorem tries_tileArgs (x : AllTilesArgs) (β β' : ℕ) :
    (tileArgs x β β').tries = triesBefore x β (β' + 1) := by
  rw [triesBefore, tilesBefore_succ, allTries_snoc]
  rfl



/-! ## One row, and all rows -/


/-- The time of all rows. -/
theorem time_le (nB T : ℕ) : 12 + (nB * (4 + (nB * (T + 27) + 16)) + 4)
    ≤ nB * (nB * (T + 80) + 40) + 30 := by
  grind

end AllTiles

