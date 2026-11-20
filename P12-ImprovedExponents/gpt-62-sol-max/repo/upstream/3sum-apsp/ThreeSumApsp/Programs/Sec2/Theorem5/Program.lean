/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.LibraryContracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize
public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import ThreeSumApsp.Util.Sum
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.BandCounters
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Binomials
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Coefficients
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Digits
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Subsets
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.CountingSort

/-! Shared tables and encoding operations used by the pruned solver. -/

@[expose] public section

namespace Light.Sec2



/-- The retained procedures of Theorem 5, at their original numbers. -/
def program5 : Program :=
  [.skip, .skip, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
    digitsBody, coefBody, bandArrayBody, encStepBody] ++ List.replicate 15 .skip

/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 : ℕ := 2000

/-- The procedures that the shared stage calls meet their entries. -/
theorem sharedCallees_of_prefix (R : Program) (lim : Limits) (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 where
  pow := pow_entry std (at_prefix rfl R) (by decide)
  binom := binom_entry std (at_prefix rfl R) (by decide)
  sqrt := sqrt_entry (at_prefix rfl R) (by decide)
  coef := coef_entry std (at_prefix rfl R) (by decide)
  subsets := subsets_entry std (at_prefix rfl R) (by decide)
  counters := counters_entry std (at_prefix rfl R) (by decide)
  digits := digits_entry std (at_prefix rfl R) (by decide)

end Light.Sec2
