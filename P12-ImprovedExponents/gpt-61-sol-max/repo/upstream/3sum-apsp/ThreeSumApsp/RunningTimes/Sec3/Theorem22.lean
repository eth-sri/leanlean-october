/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Machine.Solving
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.TimeBound
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.TimeBound
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Util.Asymptotics.LogU
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total
public import ThreeSumApsp.Programs.Sec3.Theorem19.BruteForceClaim
public import ThreeSumApsp.Programs.Sec3.Theorem19.ChooseBySize
public import ThreeSumApsp.Programs.Sec3.Corollary15_16.CountAndDetect
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Programs.Sec4.Corollary26.AllInstances
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.ParameterSteps
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.Lang.TopProcedure
public import PaperStatements
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
public import ThreeSumApsp.TimeClaims.Sec3.Theorem19
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Program
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.TimeBound
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout
public import ThreeSumApsp.TimeClaims.Sec3.Theorem21_22

/-!
# Theorem 22 on the word RAM

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).
-/

public section

open ThreeSumApsp

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/

/-- Theorem 21(a): 3SUM from Exact Triangle, through Convolution-3SUM. -/
def claim_theorem_21a :=
  Theorem21a.of_CH20_VW13 _ ChanHe.claim_CH20_Theorem_5_1
    claim_VW13_Theorem_4_3

/-! ## A bound for Exact Triangle, plugged into Theorem 21 -/

/-- 3SUM in `O(n^a)` time for every `a > 2 − δ/2`. -/
def threeSum_of_uniform {δ} {e} hδ
    (hu : Claim.ExactTriangleUniform lightModel δ e) {a} (ha : 2 - δ / 2 < a) :=
  FromClaims.solvedInTime_of_claim realized_threeSum
    ((threeSum_of_uniform_theorem_21a _ e hδ hu claim_theorem_21a).mono
      fun _ hf => hf.upperBigOPow ha)

end Light.Sec3
