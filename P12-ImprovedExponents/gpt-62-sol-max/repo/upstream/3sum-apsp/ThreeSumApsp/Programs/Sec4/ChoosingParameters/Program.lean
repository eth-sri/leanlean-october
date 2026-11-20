/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Ceiling
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.InnerProduct
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Pad
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program

/-! Assemble the shared utilities for rational parameters. -/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

/-! ## The program -/

/-- The bodies of the procedures number 58, 59, …, 73 (61 is not used). -/
def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, .skip, query31Body] ++
    List.replicate 6 .skip ++ [ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G

/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by assumption), length_base58]
  exact h

/-! ## The program on the word RAM -/

end Light.Sec4
