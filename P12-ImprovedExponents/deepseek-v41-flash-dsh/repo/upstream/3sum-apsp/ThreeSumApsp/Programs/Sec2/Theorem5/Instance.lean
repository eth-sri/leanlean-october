/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.SortedFacts
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.TacticsShort

/-!
# Theorem 5: an instance of the task, in the terms of Section 2

An instance of the thin matrix product is given by lists in the memory. This file reads them as the
matrices X and Y and the set W of Section 2, and has the facts that link the two descriptions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

def thinI (x : ThinInst) (i : ℕ) : ℕ := x.WI.getD i 0

/-- The column of the wanted position number i. -/
def thinJ (x : ThinInst) (i : ℕ) : ℕ := x.WJ.getD i 0

variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}

section positions

variable {i : ℕ}

/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

/-- A number of a wanted position is an index of the list of the positions. -/
theorem _root_.Light.ThinInst.Pre.lt_lenZip (hpre : x.Pre μ fr) (hi : i < x.w) :
    i < (x.WI.zip x.WJ).length := by
  simp [hpre.lenWI, hpre.lenWJ, hi]

theorem thinI_eq (h : i < x.WI.length) : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq (h : i < x.WJ.length) : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wi + i) = (thinI x i : ℕ) := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wj + i) = (thinJ x i : ℕ) := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end positions

/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i : ℕ} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  rw [thinI_eq (hpre.lt_lenWI hi), thinJ_eq (hpre.lt_lenWJ hi)]
  unfold thinOut
  rw [List.getD_eq_getElem _ _ (by simpa using hpre.lt_lenZip hi), List.getElem_map,
    List.getElem_zip]

end Light.Sec2