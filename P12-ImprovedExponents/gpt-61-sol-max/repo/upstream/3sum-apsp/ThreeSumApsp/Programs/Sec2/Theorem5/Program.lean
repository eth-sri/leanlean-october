/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.LibraryContracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize
public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Util.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.BandCounters
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Binomials
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Coefficients
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Digits
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Subsets
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.CountingSort
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith

/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/

@[expose] public section

namespace Light.Sec2



/-- The program of Theorem 5.  The numbers of the procedures begin with 1; number 0 is empty. -/
def program5  :=
  [.skip, .skip, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
    digitsBody, coefBody, bandArrayBody, encStepBody] ++ List.replicate 15 .skip

/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
def at_prefix {p : ℕ} {body} (h : program5[p]? = some body) R :=
  getElem?_append_of_eq_some h R

/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 := 2000

/-- The procedures that the shared stage calls meet their entries. -/
theorem sharedCallees_of_prefix R lim (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 where
  pow := pow_entry std (at_prefix rfl R) (by decide)
  binom := binom_entry std (at_prefix rfl R) (by decide)
  sqrt := sqrt_entry (at_prefix rfl R) (by decide)
  coef := coef_entry std (at_prefix rfl R) (by decide)
  subsets := subsets_entry std (at_prefix rfl R) (by decide)
  counters := counters_entry std (at_prefix rfl R) (by decide)
  digits := digits_entry std (at_prefix rfl R) (by decide)

end Light.Sec2
