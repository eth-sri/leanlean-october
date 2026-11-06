/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.LightModel
import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host

/-!
# APSP from the (min,+)-product: the claim

The running time of the host (`apTime`, `isHost_ap`) in the form of the claim
`ApspFromMinPlus`: `⌈log₂ n⌉ + 1` times the sum of the time of a (min,+)-product of
matrices whose entries are bounded by `3nu` and of `O(n² (1 + log(nu)))` (for Theorem 21(b)).
-/


namespace Light.Sec3

open ThreeSumApsp

/-- APSP from the (min,+)-product, for programs of the light language. -/
theorem claim_apspFromMinPlus : Claim.ApspFromMinPlus lightModel := by
  refine ⟨3, 135, by norm_num, fun T hT => isHost_ap.solvedIn hT fun Tn hTn n U u hn hU hu => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by simp_all
  have hτ : Tn n (3 * (n * U)) ≤ T n (3 * (n * u)) := by
    grind [Nat.mul_pos, mul_le_mul_of_nonneg_left]
  have hlog : 0 ≤ logU (3 * (n * u)) :=
    Real.log_nonneg (by simp)
  have hτ0 : 0 ≤ T n (3 * (n * u)) := by grind
  have hc0 : 0 ≤ (Nat.clog 2 n : ℝ) := by positivity
  have hns : n ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs1 : 1 ≤ n ^ 2 := by nlinarith
  have hsℓ : 0 ≤ n ^ 2 * logU (3 * (n * u)) := by positivity
  simp [apTime]
  rw [← sq _]
  -- `t ≤ τ` are the time of the solver and its bound, `ℓ = log (3nu)`, `c` is the number of rounds
  -- and `s = n²`
  generalize Tn n _ = t at hτ ⊢
  generalize T n _ = τ at hτ hτ0 ⊢
  generalize logU _ = ℓ at hsℓ ⊢
  generalize Nat.clog 2 n = c at hc0 ⊢
  generalize (n : ℝ) ^ 2 = s at hns hs1 hsℓ ⊢
  have hround : t + 23 * s + 29 ≤ τ + 135 * s * (1 + ℓ) := by linarith
  calc c * (t + 23 * s + 29) + 53 * s + 17 * n + 65
      ≤ c * (τ + 135 * (s * (1 + ℓ))) + τ + 135 * s * (1 + ℓ) := by
        linarith [mul_le_mul_of_nonneg_left hround hc0]
    _ = (c + 1) * (τ + 135 * (s * (1 + ℓ))) := by ring
