/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Util.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Programs.Tasks

/-!
# Theorem 5: an instance of the task, in the terms of Section 2

An instance of the thin matrix product is given by lists in the memory. This file reads them as the
matrices X and Y and the set W of Section 2, and has the facts that link the two descriptions.
-/

@[expose] public section

namespace Light.Sec2



/-- The row of the wanted position number i. -/
def thinI (x : ThinInst) i := x.WI.getD i 0

/-- The column of the wanted position number i. -/
def thinJ (x : ThinInst) i := x.WJ.getD i 0

variable {x : ThinInst} {m : ℕ} {μ : Light.Memory} {fr : ℕ}

section

variable {i : ℕ}

variable (hpre : x.Pre μ fr) (hi : i < x.w)

include hpre hi in
/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI  : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

include hpre hi in
/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ  : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

theorem thinI_eq h : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq h : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

include hpre hi in
/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt  : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

include hpre hi in
/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt  : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

include hpre hi in
/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI  : μ (x.wi + i) = thinI x i := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

include hpre hi in
/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ  : μ (x.wj + i) = thinJ x i := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end

/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  ram_safe [Light.Sec2.thinI, Light.Sec2.thinJ, thinOut]

end Light.Sec2
