/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory

/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-! ## The program -/


/-- The addresses of the areas of Section 4, which lie one behind the other from WD on. -/
def preCoreAddr  :=
  .set 9 (M (v 7 +' k 30)) ;;
  .set 10 (M (v 7 +' k 9)) ;;
  .set 11 (v 9 +' v 0) ;;
  .set 12 (v 11 +' v 0) ;;
  .set 13 (v 12 +' v 0 +' v 1) ;;
  .set 14 (v 13 +' k 1) ;;
  .set 15 (v 1 -' v 2) ;;
  .set 16 (v 14 +' v 10 *' v 10)

/-- The trie array starts as [0], of length 1; then the tries of all tiles. -/
def preCoreFinish  :=
  .store (v 16) (k 0) ;;
  .store (v 13) (k 1) ;;
  .call 51 [M (v 7 +' k 26), M (v 7 +' k 27), v 10,
    M (v 7 +' k 10), v 14, v 16, v 13, v 11, v 12, v 0, v 15] 8

/-- What the locals hold after the shared stage; r is its result. -/
def preShared (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [p.L, p.m, t, p.N, p.D, aX, aY, b0, r]

/-- What the locals hold after the addresses have been computed. -/
def preLocals p t aX aY b0 r :=
  preShared p t aX aY b0 r ++ [(aWD p b0 : ℤ), p.nB, aCUR p b0, aBOX p b0, aFP p b0, aROOTS p b0,
    (p.m - t : ℕ), aTR p b0]

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : ThreeSumApsp.IntMatrix p.N (D p.m)} {Y : ThreeSumApsp.IntMatrix (D p.m) p.N}
  {U : ℤ} {μ : Light.Memory}

/-! ## The addresses -/

/-! ## The tries -/

/-- The arguments of the call of allTiles, and the data behind them. -/
def allArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : ThreeSumApsp.IntMatrix p.N (D p.m)) (Y : ThreeSumApsp.IntMatrix (D p.m) p.N) :
    AllTilesArgs where
  L := p.L
  m := p.m
  t := t
  nB := p.nB
  encA := encRow p hmL X
  encB := encCol p hmL Y
  aENCA := p.aENCA b0
  aENCB := p.aENCB b0
  aR := aROOTS p b0
  tr := aTR p b0
  cap := trieCap p t
  fp := aFP p b0
  cur := aCUR p b0
  box := aBOX p b0

/-- The trie area with the array [0], after the two stores. -/
theorem trieMem_start p t b0 μ :
    TrieMem (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1) (aTR p b0)
      (trieCap p t) (aFP p b0) [0] := by
  obtain ⟨⟩ := areas p t b0
  refine ⟨fun i hi => ?_, Function.update_self .., by simp [trieCap], Or.inl (by omega)⟩
  grind

/-! ## The routine -/

end Light.Sec4
