/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Ceiling
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.InnerProduct
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Pad
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program

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

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, .skip, query31Body,
    .skip, .skip, .skip, .skip, .skip,
    .skip, ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G

/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by trivial), length_base58]
  exact h

/-! ## The program on the word RAM -/

end Light.Sec4
