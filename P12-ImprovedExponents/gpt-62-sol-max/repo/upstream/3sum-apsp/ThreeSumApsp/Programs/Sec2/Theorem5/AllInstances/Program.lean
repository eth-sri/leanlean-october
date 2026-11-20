/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Sec2.Theorem5.WordSize
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import ThreeSumApsp.Util.Sum
public import ThreeSumApsp.Programs.Sec2.Theorem5.Program

/-! Extend the table routines with the fallback thin-product procedure. -/

@[expose] public section

namespace Light.Sec2



/-- The program of the thin matrix product on all instances. -/
def programThin : Program := program5 ++ [.skip, thinBruteBody, .skip]

end Light.Sec2
