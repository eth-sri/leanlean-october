/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.LibraryContracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.BandCounters
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Binomials
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Coefficients
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Digits
public import ThreeSumApsp.Programs.Sec2.Theorem5.Tables.Subsets
public import ThreeSumApsp.Util.CountingSort

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

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 : ℕ := 2000

end Light.Sec2
