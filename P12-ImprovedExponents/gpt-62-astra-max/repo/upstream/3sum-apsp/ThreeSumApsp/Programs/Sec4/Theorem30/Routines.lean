/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles
public import ThreeSumApsp.Programs.Sec4.Theorem30.FillList
public import ThreeSumApsp.Programs.Sec4.Theorem30.Horner
public import ThreeSumApsp.Programs.Sec4.Theorem30.Insert
public import ThreeSumApsp.Programs.Sec4.Theorem30.Lookup
public import ThreeSumApsp.Programs.Sec4.Theorem30.NineNext
public import ThreeSumApsp.Programs.Sec4.Theorem30.OutDigits
public import ThreeSumApsp.Programs.Sec4.Theorem30.Preprocessing
public import ThreeSumApsp.Programs.Sec4.Theorem30.Query
public import ThreeSumApsp.Programs.Sec4.Theorem30.QuerySum
public import ThreeSumApsp.Programs.Sec4.Theorem30.Scatter
public import ThreeSumApsp.Programs.Sec4.Theorem30.StarFirst
public import ThreeSumApsp.Programs.Sec4.Theorem30.SumTen
public import ThreeSumApsp.Programs.Sec4.Theorem30.Tile

/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4

/-- The bodies of the procedures number 40, 41, …, 53. -/
def procs40 : List Stmt :=
  [nineFirstBody, nineNextBody, scatterBody, starFirstBody, hornerBody, lookupBody, insertBody,
    newRootBody, sumTenBody,
    fillListBody, tileBody, allTilesBody, outDigitsBody, queryCoreBody]

/-- The program P holds the routines of Section 4 at their numbers. -/
def Has40 (P : Program) : Prop := ∀ i < 14, P[40 + i]? = procs40[i]?

/-- The specifications of all the routines of Section 4. -/
structure Specs40 (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  starFirst : StarFirstSpec lim P
  horner : HornerSpec lim P
  lookup : LookupSpec lim P
  insert : InsertSpec lim P
  newRoot : NewRootSpec lim P
  sumTen : SumTenSpec lim P
  fillList : FillListSpec lim P
  tile : TileSpec lim P
  allTiles : AllTilesSpec lim P
  outDigits : OutDigitsSpec lim P
  queryCore : QueryCoreSpec lim P

/-- **Every program that holds the routines of Section 4 at their numbers meets all their
specifications.** -/
theorem specs40 {lim : Limits} {P : Program} (h : Has40 P) (hs : Std lim) : Specs40 lim P := by
  have nineFirst : NineFirstSpec lim P := nineFirst_spec (h 0 (by omega)) hs
  have nineNext : NineNextSpec lim P := nineNext_spec (h 1 (by omega)) hs
  have scatter : ScatterSpec lim P := scatter_spec (h 2 (by omega)) hs
  have starFirst : StarFirstSpec lim P := starFirst_spec (h 3 (by omega)) hs
  have horner : HornerSpec lim P := horner_spec (h 4 (by omega)) hs
  have lookup : LookupSpec lim P := lookup_spec (h 5 (by omega)) hs
  have insert : InsertSpec lim P := insert_spec (h 6 (by omega)) hs
  have newRoot : NewRootSpec lim P := newRoot_spec (h 7 (by omega)) hs
  have sumTen : SumTenSpec lim P := sumTen_spec (h 8 (by omega)) lookup hs
  have fillList : FillListSpec lim P := fillList_spec
    (h 9 (by omega)) nineFirst nineNext starFirst horner insert sumTen
  have tile : TileSpec lim P := tile_spec (h 10 (by omega)) newRoot fillList
  have allTiles : AllTilesSpec lim P := allTiles_spec (h 11 (by omega)) tile
  have outDigits : OutDigitsSpec lim P := outDigits_spec (h 12 (by omega))
  have queryCore : QueryCoreSpec lim P :=
    queryCore_spec (h 13 (by omega)) ⟨nineFirst, nineNext, scatter, horner, lookup⟩
  exact ⟨nineFirst, nineNext, scatter, starFirst, horner, lookup, insert, newRoot, sumTen,
    fillList, tile, allTiles,
    outDigits, queryCore⟩

/-- A list that has forty procedures, then the routines of Section 4, then anything, holds them at
their numbers. -/
theorem has40_of_append {A B : List Stmt} (hA : A.length = 40) : Has40 (A ++ procs40 ++ B) := by
  intro i hi
  have hlen : procs40.length = 14 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

end Light.Sec4
