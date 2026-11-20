/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

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
  have hn' : (1 : ℝ) ≤ n := by simp_all
  have hτ : (Tn n (3 * (n * U)) : ℝ) ≤ T n (3 * (n * u)) := by
    refine hTn n (3 * (n * U)) _ hn (by nlinarith) ?_
    simp_all +arith
  have hlog : 0 ≤ logU (3 * (n * u)) :=
    by apply Real.log_nonneg <;> grind
  have hns : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have hsℓ : 0 ≤ n ^ 2 * logU (3 * (n * u)) := by positivity
  simp [apTime]
  push_cast
  nlinarith

end Light.Sec3
