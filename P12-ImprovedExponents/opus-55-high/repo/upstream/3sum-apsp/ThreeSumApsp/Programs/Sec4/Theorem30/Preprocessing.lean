/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec4.Theorem30.Directory

/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/


namespace Light.Sec4

open ThreeSumApsp

/-! ## The program -/

namespace PreCore

/- The local variables of preCore: the arguments L, m, t, N, D, aX, aY, b0; a local for results
that are not used; the address of WD, the number nB, the addresses of CUR, BOX, FP, ROOTS, the
number m - t, and the address of TR. -/
slots Levels Inner Switch Size Width MatX MatY Base Void Digits Bands Cur Box Free Roots Last Tries

end PreCore

open PreCore in
/-- The addresses of the areas of Section 4, which lie one behind the other from WD on. -/
def preCoreAddr : Stmt :=
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Cur (v Digits +' v Levels) ;;
  .set Box (v Cur +' v Levels) ;;
  .set Free (v Box +' v Levels +' v Inner) ;;
  .set Roots (v Free +' k 1) ;;
  .set Last (v Inner -' v Switch) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open PreCore in
/-- The trie array starts as [0], of length 1; then the tries of all tiles. -/
def preCoreFinish : Stmt :=
  .store (v Tries) (k 0) ;;
  .store (v Free) (k 1) ;;
  .call Proc.allTiles [M (v Base +' k Dir.encA), M (v Base +' k Dir.encB), v Bands,
    M (v Base +' k Dir.leaves), v Roots, v Tries, v Free, v Cur, v Box, v Levels, v Last] Void

open PreCore in
/-- preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on. -/
def preCoreBody : Stmt :=
  .call Sec2.pShared [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  preCoreAddr ;;
  preCoreFinish

/-- What the locals hold after the shared stage; r is its result. -/
def preShared (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [p.L, p.m, t, p.N, p.D, aX, aY, b0, r]

/-- What the locals hold after the addresses have been computed. -/
def preLocals (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  preShared p t aX aY b0 r ++ [(aWD p b0 : ℤ), p.nB, aCUR p b0, aBOX p b0, aFP p b0, aROOTS p b0,
    (p.m - t : ℕ), aTR p b0]

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {μ : ℕ → ℤ}

/-! ## The addresses -/

/-! ## The tries -/

/-- The arguments of the call of allTiles, and the data behind them. -/
def allArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    AllTilesArgs := ⟨p.L, p.m, t, p.nB, encRow p hmL X, encCol p hmL Y, p.aENCA b0, p.aENCB b0, aROOTS p b0, aTR p b0, trieCap p t, aFP p b0, aCUR p b0, aBOX p b0⟩

/-- The trie area with the array [0], after the two stores. -/
theorem trieMem_start (p : Sec2.Par) (t b0 : ℕ) (μ : ℕ → ℤ) :
    TrieMem (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1) (aTR p b0)
      (trieCap p t) (aFP p b0) [0] := by
  obtain ⟨⟩ := areas p t b0
  refine ⟨fun i hi => ?_, Function.update_self .., by simp [trieCap], by omega⟩
  grind

/-! ## The routine -/
