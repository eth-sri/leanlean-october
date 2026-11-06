/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import Mathlib.Data.Nat.Log
public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Util.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec2.Theorem5.Program

/-!
# The running-time claim "Theorem 5" for the light model, for the program of Theorem 5

programThin is program5 followed by regimeBody (the test whether an instance is in the regime of
Theorem 5), thinBruteBody (the brute force, for the instances outside it) and thinBody (the solver
for all instances). claim_theorem_5: it solves the thin matrix product on all instances, and for D ≥
4 a power of four, N ≥ D^18, w ≤ N²/√D and entries of at most N^c its time is at most a constant
times N² log² D / D^{1/18}. This is thin_claim for the program and the solver of Theorem 5.
-/

@[expose] public section

namespace Light.Sec2



/-- The program of the thin matrix product on all instances. -/
def programThin : Program := program5 ++ [.skip, thinBruteBody, .skip]

end Light.Sec2
