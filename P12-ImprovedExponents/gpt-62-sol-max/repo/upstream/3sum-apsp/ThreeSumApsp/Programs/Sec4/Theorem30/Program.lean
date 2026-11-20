/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Program
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Sec4.Theorem30.Preprocessing
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.Routines

/-! The retained routines of Theorem 30, at their original numbers. -/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The procedures number 0 to 57: Section 2's program for the thin matrix product (0 to 28), eleven
unused numbers, the routines of Section 4, the two routines that know the memory map, and the two
routines of the offline form. -/
def base58 : Program :=
  Sec2.programThin ++ List.replicate 11 .skip ++ procs40 ++
    [.skip, queryAtBody, .skip, .skip]

theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-- The constant of the shared stage. -/
def cShared30 : ℕ := 12 * Sec2.cShared5 + 600

theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [.skip, queryAtBody, .skip, .skip] ++ R) rfl
  assumption

end Light.Sec4
