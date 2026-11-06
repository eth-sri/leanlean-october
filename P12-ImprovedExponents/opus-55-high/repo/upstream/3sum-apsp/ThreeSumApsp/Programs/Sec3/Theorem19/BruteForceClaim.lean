/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.LightModel
import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce

/-!
# The running time of brute force (the proof of Theorem 19)

The `100 n³ + 100` steps of brute are within the form `C n³ (1 + log u)` in which the running times
for Exact Triangle with weights of absolute value at most `u` are stated (`claim_bruteForce`).
-/


namespace Light.Sec3

open ThreeSumApsp

/-- "Smaller instances are solved by brute force" (proof of Theorem 19): Exact Triangle is
solved in time `C n³ (1 + log u)`, where `u` bounds the absolute values of the weights.  The factor
`1 + log u` is not needed here; it belongs to the form of the running times for this problem. -/
theorem claim_bruteForce : Claim.BruteForce lightModel := by
  refine ⟨200, [bruteBody 1, scanBody], 0, fun n _ => tBrute n, bruteNeed, ⟨2, 1, fun n U => ?_⟩,
    brute_solves, fun n U u hn _ _ => ?_⟩
  · grind [polyBound, bruteNeed]
  · have hlog : 0 ≤ logU u := Real.log_nonneg (by simp)
    have hn1 : 1 ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by simp_all)
    calc tBrute n = 100 * (n : ℝ) ^ 3 + 100 := by simp_all [tBrute]
      _ ≤ 200 * (n ^ 3 * 1) := by linarith
      _ ≤ 200 * (n ^ 3 * (1 + logU u)) := by gcongr; linarith
