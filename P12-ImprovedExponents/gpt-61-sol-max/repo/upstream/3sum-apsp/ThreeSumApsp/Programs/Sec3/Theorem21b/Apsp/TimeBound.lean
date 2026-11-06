/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host

/-!
# APSP from the (min,+)-product: the claim

The running time of the host (`apTime`, `isHost_ap`) in the form of the claim
`ApspFromMinPlus`: `⌈log₂ n⌉ + 1` times the sum of the time of a (min,+)-product of
matrices whose entries are bounded by `3nu` and of `O(n² (1 + log(nu)))` (for Theorem 21(b)).
-/

public section

namespace Light.Sec3

open ThreeSumApsp

/-- APSP from the (min,+)-product, for programs of the light language. -/
theorem claim_apspFromMinPlus : Claim.ApspFromMinPlus lightModel := by
  refine ⟨3, 135, by norm_num, fun T hT => isHost_ap.solvedIn hT fun Tn hTn n U u hn hU hu => ?_⟩
  have  : (1 : ℝ) ≤ n := mod_cast hn
  have  : (Tn n (3 * (n * U)) : ℝ) ≤ T n (3 * (n * u)) := by
    refine hTn n (3 * (n * U)) _ hn (by bound) ?_
    push_cast
    bound
  have  : 0 ≤ logU (3 * (n * u)) :=
    Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _))



  have  : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have  : 0 ≤ (n : ℝ) ^ 2 * logU (3 * (n * u)) := by positivity
  simp only [apTime]
  push_cast
  rw [← sq (n : ℝ)]
  -- `t ≤ τ` are the time of the solver and its bound, `ℓ = log (3nu)`, `c` is the number of rounds
  -- and `s = n²`
  nlinarith

end Light.Sec3
