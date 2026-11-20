module

import ThreeSumApsp.Lang.WhileShape

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Tile
public import ImprovedExponents.PrunedProgram.Tiles.Contracts

@[expose] public section

/-!
# The trie of one tile, on pruned encodings

The routine first allocates the root, then verifies each pass that fills a given star count.
It only passes the encodings to `fillList`; the reads there are covered by `SegOn`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace TileP

/-- What the memory μ' holds during the loop: the trie array T, the roots, with that of the tile
behind the older ones, and the two encodings at the leaves with few symbols `P₀`; the cells that
the routine does not own are as in μ. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (Tile.Mem)
structure Mem (μ μ' : ℕ → ℤ) (x : TileArgs) (T : List ℤ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp T
  roots : SegN μ' x.aR (x.s.roots ++ [x.s.cells.length])
  segA : SegOn x.m μ' x.aA x.encA
  segB : SegOn x.m μ' x.aB x.encB
  same : SameOn x.Kept μ μ'

end TileP

open TileP in
/-- **tile on pruned encodings** meets its specification. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean (tile_spec)
theorem tileP_spec {lim : Limits} {P : Program} (hP : P[Proc.tile]? = some tileBody)
    (hNew : NewRootSpec lim P) (hFill : FillListSpecP lim P) : TileSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨tileBody, hP, ?_⟩
  have hlayout := C.ctx.layout
  light_facts C C.ctx C.ctx.std
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  unfold tTile
  -- root := newRoot(tr, fp)
  light_call (hNew x.tr x.cap x.fp x.s.cells μ C.trie (by omega) (by omega) (by omega) _
    (by omega)) with _ μ₁ ⟨rfl, htrie, same⟩
  -- mem[ra] := root
  light_step
  -- while e ≤ mt
  refine Ends.whileShapeCosts (fun e void ν =>
      ⟨frame [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L,
        (x.m - x.t : ℕ), e, x.s.cells.length, void], ν⟩)
    (fun e _ ν => Mem μ ν x (Tile.trieAt x e)) (x.m - x.t + 1)
    (fun e => tFillList x.L (starBoxes x.L x.m x.t e).length + 30) 0
    (Function.update μ₁ (x.aR + x.s.roots.length) (x.s.cells.length : ℤ))
    ⟨htrie.keep, SegN.snoc C.roots.keep _, C.segA.keep, C.segB.keep, by light_keep⟩ ?_
    (fun _ _ h => ⟨h.trie, h.roots, h.same⟩)
    (first := by simp; exact (frame_append_zeros _ 1).symm)
    (hT := by
      have hsum := Tile.time_le x.L x.m x.t (x.m - x.t + 1)
      have htest y : 1 + (1 + 1 + 1) + 1 + 1 + y = (6 : ℕ) + y := by omega
      light_time [Cond.cost, Expr.cost, htest])
  intro e void ν he hM
  have he' : e ≤ x.m - x.t := by omega
  -- the trie of the tile has the number s.roots.length, and its root is the last one
  have hroot := x.s.root_new
  have hfill := hFill (Tile.fillArgs x e) ν
    { ctx := C.ctx, stars_le := he', root_ne := hroot.trans_ne C.rep.length_pos.ne'
      rep := fillUpTo_rep (arrT x.encA) (arrT x.encB) x.m x.t x.s C.rep e
      trie := hM.trie, segA := hM.segA, segB := hM.segB
      room := (Tile.room (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length x.s.cells
        he').trans C.room }
  simp only [Tile.fillArgs, FillListArgs.vals, FillListArgs.root, FillListArgs.boxes, hroot]
    at hfill
  -- fillList(e, root, …)
  light_call (hfill _ (by omega)) with void' μ₂ ⟨htrie, same⟩
  light_step
  exact ⟨void', μ₂, rfl, htrie, hM.roots.keep, hM.segA.keep, hM.segB.keep, by light_keep [hM.same]⟩

end Light.Sec4
