/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Frames

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-! The tries of all tiles, built by calling `tile` in row-major order. -/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace AllTiles

registers [EncA, EncB, Bands, Leaves, RootTab, Tries, Free, Cur, Box, Levels, Last, RowBand,
  ColBand, Void]

end AllTiles

open AllTiles in
/-- allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt). -/
def allTilesBody : Stmt :=
  .for RowBand (v Bands) (.for ColBand (v Bands)
    (.call Proc.tile [v EncA +' v RowBand *' v Leaves, v EncB +' v ColBand *' v Leaves,
      v RootTab +' (v RowBand *' v Bands +' v ColBand), v Tries, v Free, v Cur, v Box, v Levels,
      v Last] Void))

namespace AllTiles

/-! ## The invariant and one tile -/

variable {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The tries and the roots of the tiles before the tile (β, β'). -/
def triesBefore (x : AllTilesArgs) (β β' : ℕ) : TrieStore :=
  allTries x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')

/-- What the memory μ' holds before the tile (β, β'): the tries and the roots of the tiles before
it; nothing below cur or behind the trie area has changed since μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp (triesBefore x β β').cells
  roots : SegN μ' x.aR (triesBefore x β β').roots
  same : SameOn x.Kept μ μ'

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
private theorem length_roots_triesBefore (x : AllTilesArgs) (β β' : ℕ) :
    (triesBefore x β β').roots.length = β * x.nB + β' := by
  rw [triesBefore, length_roots_allTries, length_tilesBefore]

/-- The tries after the tile (β, β'). -/
private theorem tries_tileArgs (x : AllTilesArgs) (β β' : ℕ) :
    (tileArgs x β β').tries = triesBefore x β (β' + 1) := by
  rw [triesBefore, tilesBefore_succ, allTries_snoc]
  rfl

end AllTiles

end Light.Sec4
