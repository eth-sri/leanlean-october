/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline

/-!
# Section 4.4: the costs of the programs with rational parameters

Bounds for the time and the space of the preprocessing and for the time of a query. `CostsWithin`
says of two bounds tp and tq that they dominate the two costs of Theorem 30. A quantity that is
bounded for m < m₀ and within a constant times a cost for m ≥ m₀ is then within a constant times the
bound (`exists_le_of_small_of_large`). The overheads are absorbed by the cost expression (8) of
Theorem 30: padding, copying and filling cost O(N 4^m), and N 4^m ≤ N 10^L/(√K N₀), because K N₀ 4^m
≤ 7^L (`N_mul_pow_le_cost8`); computing L and t costs O(L). For m < m₀ everything is bounded by a
constant. This gives the results that the end theorems use: `exists_tPre31_le`,
`exists_tQuery31_le`, `exists_tOffline32_le`, `exists_structEnd_sub_le`, `exists_lim31_depth_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

section
variable (G : RatParams)

/-- A quantity that is bounded below the threshold, and at most a constant times a cost from the
threshold on, is at most a constant times every bound t ≥ 1 that dominates the cost. -/
theorem exists_le_of_small_of_large {C } (hC : 0 ≤ C) {S K } (hS : 0 ≤ S) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D₀ : ℕ) (cost t z : ℝ), 1 ≤ t → (G.m₀ ≤ logFour D₀ → cost ≤ C * t) →
      (logFour D₀ < G.m₀ → z ≤ S) → (G.m₀ ≤ logFour D₀ → z ≤ K * cost + S) → z ≤ A * t := by
  refine ⟨S + K * C, by positivity, fun D₀ cost t z ht hcost hsmall hlarge => ?_⟩
  have hSt := le_mul_of_one_le_right hS ht
  by_cases hm : logFour D₀ < G.m₀
  · linarith [hsmall hm, mul_nonneg hK (mul_nonneg hC (by linarith))]
  · linarith [hlarge (by omega), mul_le_mul_of_nonneg_left (hcost (by omega)) hK]

/-! ### The preprocessing -/

/-! ### A query -/

end

/-! ### Space and the nesting of calls -/

end Light.Sec4
