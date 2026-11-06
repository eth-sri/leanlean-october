/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The trie of one tile

Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile". Its proof: "We compute the values of the boxes in increasing
order of their number of stars." The routine takes a root for the trie of the tile and writes it
into the table of roots (Tile.Mem.newRoot). Then, for e = 0, …, m - t, it puts the boxes with e
stars into the trie (tileRound); for e ≥ 1 their values are sums of values looked up in the trie.
The invariant Tile.Inv says what the memory holds before the boxes with e stars; Tile.round takes it
from e to e + 1, and tile_spec is the root and the loop.
-/


namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace Tile

/- The local variables of tile: the arguments aA, aB, ra, tr, fp, cur, box, L, mt; the number e of
stars, the root of the trie of the tile, and a local for a result that is not used. -/
slots EncA EncB RootCell Tries Free Cur Box Levels Last Stars Root Void

end Tile

open Tile in
/-- The boxes with e stars go into the trie; on to the next number of stars. -/
def tileRound : Stmt :=
  .call Proc.fillList [v Stars, v Root, v EncA, v EncB, v Tries, v Free, v Cur, v Box, v Levels,
    v Last] Void ;;
  .set Stars (v Stars +' k 1)

open Tile in
/-- tile(aA, aB, ra, tr, fp, cur, box, L, mt): a root for the trie of the tile, noted in the cell
ra; then the boxes with 0, 1, …, mt stars. The number of stars starts at 0, as all locals that are
not arguments. -/
def tileBody : Stmt :=
  .call Proc.newRoot [v Tries, v Free] Root ;;
  .store (v RootCell) (v Root) ;;
  .while (v Stars ≤' v Last) tileRound

namespace Tile

/-! ## The pure side -/

/-- Behind the root and the boxes with fewer than e stars there is room for the boxes with e
stars. -/
theorem room (a b : List ℤ) (L m t root : ℕ) (T : List ℤ) {e : ℕ} (he : e ≤ m - t) :
    (fillUpTo a b L m t root e (trieNew T)).length + 11 * L * (starBoxes L m t e).length
      ≤ T.length + 11 * (1 + L * (boxes L m t).card) := by
  have hused := length_fillUpTo_le_sum a b L m t root e (trieNew T)
  rw [length_trieNew] at hused
  have hlists := List.sum_map_range_mono (fun e => (starBoxes L m t e).length)
    (show e + 1 ≤ m - t + 1 by omega)
  rw [sum_length_starBoxes, List.range_succ, List.map_append] at hlists
  simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hlists
  have hmul := Nat.mul_le_mul_left (11 * L) hlists
  linarith

/-- The time: the sum over the rounds, each with the test of the loop (6 steps). -/
theorem time_le (L m t n : ℕ) :
    ∑ i ∈ Finset.range n, (6 + (tFillList L (starBoxes L m t i).length + 30))
      ≤ ((List.range n).map fun e => tFillList L (starBoxes L m t e).length + 60).sum := by
  exact Finset.sum_le_sum fun _ _ => by omega

/-! ## The memory during the loop -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ₁ μ₂ : ℕ → ℤ} {x : TileArgs} {e : ℕ} {σ : State}
  {T T' : List ℤ}




/-! ## The invariant and one round -/

/-- The trie array once the root of the tile has been taken and the boxes with fewer than e stars
are in the trie. -/
def trieAt (x : TileArgs) (e : ℕ) : List ℤ :=
  fillUpTo (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length e (trieNew x.s.cells)

/-- The arguments of the call of fillList for the boxes with e stars. -/
def fillArgs (x : TileArgs) (e : ℕ) : FillListArgs :=
  { x with e := e, tile := x.s.roots.length, roots := x.s.new.root, T := trieAt x e }



end Tile

