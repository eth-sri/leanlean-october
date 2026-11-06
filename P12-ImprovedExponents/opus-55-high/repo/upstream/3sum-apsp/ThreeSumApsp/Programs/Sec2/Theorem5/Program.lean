/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Contract
import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
import ThreeSumApsp.Programs.Sec2.Theorem5.Solver
import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.BandCounters
import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Binomials
import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Coefficients
import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Digits
import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Subsets
import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Codes
import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Gather
import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Sort

/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/


namespace Light.Sec2


/-- The program of Theorem 5.  The numbers of the procedures begin with 1; number 0 is empty. -/
def program5 : Program :=
  [.skip, sharedBody, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
   digitsBody, coefBody, bandArrayBody, encStepBody, encodeBody pEncStep pEncode, encodeBandsBody,
   Wanted.wantedBody, countSortBody, sortWantedBody, segBoundsBody, unionBody, pickBody, prunedBody,
   runTilesBody, reportBody, fillBody, copyBody, gatherBody, thm5Body]

/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  by grind

/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 : ℕ := 2000

/-- The procedures that the shared stage calls meet their entries. -/
theorem sharedCallees_of_prefix (R : Program) (lim : Limits) (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 := ⟨pow_entry std (at_prefix rfl R), binom_entry std (at_prefix rfl R), sqrt_entry (at_prefix rfl R), coef_entry std (at_prefix rfl R), subsets_entry std (at_prefix rfl R), counters_entry std (at_prefix rfl R), digits_entry std (at_prefix rfl R)⟩
