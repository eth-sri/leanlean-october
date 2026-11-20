/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Program
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.TimeBound
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout
public import ThreeSumApsp.Util.Asymptotics.LogU
public import ThreeSumApsp.TimeClaims.Sec3.Theorem21_22

/-! The reduction from 3SUM to Exact Triangle, on the word RAM. -/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/

/-- Theorem 21(a): 3SUM from Exact Triangle, through Convolution-3SUM. -/
theorem claim_theorem_21a : Claim.Theorem_21a lightModel :=
  Theorem21a.of_CH20_VW13 _ ChanHe.claim_CH20_Theorem_5_1
    claim_VW13_Theorem_4_3

/-- 3SUM in `O(n^a)` time for every `a > 2 − δ/2`. -/
theorem threeSum_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) {a : ℝ} (ha : 2 - δ / 2 < a) :
    SolvedInTime EndStatement.ThreeSum a 0 :=
  FromClaims.solvedInTime_of_claim realized_threeSum
    ((threeSum_of_uniform_theorem_21a _ e hδ hu claim_theorem_21a).mono
      fun _ hf => hf.upperBigOPow ha)

end Light.Sec3
