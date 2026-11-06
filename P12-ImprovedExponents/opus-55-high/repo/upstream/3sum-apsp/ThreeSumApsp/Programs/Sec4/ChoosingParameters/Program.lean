/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Ceiling
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.InnerProduct
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.OfflineStatement
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Pad
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Statement
import ThreeSumApsp.Programs.Sec4.Theorem30.Program

/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/


namespace Light.Sec4


/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

/-- regimeTest26(N, D) returns 1 if D^18 ≤ N and 0 if not. It changes no cell. -/
def regimeTest26Body : Stmt := Sec2.regimePow ;; .set 0 (v 9)

/-- allInstances26(N, D, w, U, x, y, wi, wj, out, fr). Locals 0 to 9 are the arguments, which are
passed on as they are; local 10 is the result of the test. -/
def allInstances26Body : Stmt :=
  .call Proc.regimeTest26 [v 0, v 1] 10 ;;
  .ite (k 0 <' v 10)
    (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
    (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)

/-! ## The program -/

/-- The bodies of the procedures number 58, 59, …, 73 (61 is not used). -/
def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, pre31Body G, query31Body,
    preMain31Body, queryMain31Body, offline32Body, offlineMain32Body, allInstances26Body,
    regimeTest26Body, ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G


/-! ## The program on the word RAM -/
