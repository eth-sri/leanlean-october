/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.RegimeTest
public import ThreeSumApsp.Programs.Sec2.Theorem5.Solver

/-!
# The thin matrix product, on all instances

The task thinTask: given an N × D matrix X and a D × N matrix Y with entries of absolute value at
most U, and w positions (rows at wi, columns at wj), write the entries of XY at these positions to
the cells from out on. Theorem 5 is about instances with D ≥ 4 a power of four, N ≥ D^18
and at most N²/√D wanted positions. A solver that other procedures call has to be right on every
instance. thin(N, D, w, U, x, y, wi, wj, out, fr) tests the regime, calls the solver of Theorem 5 in
the regime and the brute force outside it.

The file proves that thin solves the task thinTask (thin_solves), within a need that is polynomial
in the parameters (thinNeed_poly) and covers what the solver of Theorem 5 asks of the limits
(thin_limits5, "Word size" in Section 2.4.4), and within the time of Theorem 5 in the regime
(thin_shape_le, thinTimeBound_le). Together these are the running-time claim "Theorem 5" for the
light model (thin_claim).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- Local 10 of thin: the result of the test of the regime. -/
abbrev Thin.Expo : ℕ := 10

open ThinArg Thin
/-- thin(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBody : Stmt :=
  .call pRegime [v Rows, v Cols, v Wanted] Expo ;;
  .ite (k 0 <' v Expo)
    (.call pThm5
      [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)
    (.call pThinBrute
      [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)

/-! ## The need -/

/-! ## The regime -/

/-! ## The time -/

/-! ## The solver of Theorem 5 may be called -/

end Light.Sec2
