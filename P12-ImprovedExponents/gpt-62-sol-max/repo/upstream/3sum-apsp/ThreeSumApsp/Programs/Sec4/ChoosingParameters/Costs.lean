/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline

/-! Turning intrinsic query costs into uniform bounds, including below the threshold. -/

@[expose] public section

namespace Light.Sec4



section
variable (G : RatParams)

/-- A quantity that is bounded below the threshold, and at most a constant times a cost from the
threshold on, is at most a constant times every bound t ≥ 1 that dominates the cost. -/
theorem exists_le_of_small_of_large {C : ℝ} (hC : 0 ≤ C) {S K : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D₀ : ℕ) (cost t z : ℝ), 1 ≤ t → (G.m₀ ≤ logFour D₀ → cost ≤ C * t) →
      (logFour D₀ < G.m₀ → z ≤ S) → (G.m₀ ≤ logFour D₀ → z ≤ K * cost + S) → z ≤ A * t := by
  refine ⟨S + K * C, by positivity, fun D₀ cost t z ht hcost hsmall hlarge => ?_⟩
  have hsplit : (S + K * C) * t = S * t + K * (C * t) := by ring
  have hSt : S ≤ S * t := le_mul_of_one_le_right hS ht
  rw [hsplit]
  by_cases hm : logFour D₀ < G.m₀
  · linarith [hsmall hm, mul_nonneg hK (mul_nonneg hC (by linarith : (0 : ℝ) ≤ t))]
  · linarith [hlarge (by omega), mul_le_mul_of_nonneg_left (hcost (by omega)) hK]

/-! ### A query -/

/-- **The time of a query** is at most a constant times every bound tq ≥ 1 that, from the threshold
on, dominates the cost L ∑ α_d of Theorem 30. -/
theorem exists_tQuery31_le {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tq : ℝ}, 1 ≤ tq → (G.m₀ ≤ logFour D₀ → G.Hyp N D₀) →
      (G.m₀ ≤ logFour D₀ → G.queryCost D₀ ≤ C * tq) → (tQuery31 G D₀ : ℝ) ≤ A * tq := by
  obtain ⟨K, hK0, hK⟩ := exists_tQueryAt_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tq} ht hHyp hcost =>
    hA D₀ _ tq _ ht hcost (fun hm => ?_) fun hm => ?_⟩
  · -- an inner product of D ≤ 4^m₀ summands
    have hD := (Nat.clog_le_iff_le_pow (by norm_num)).1 hm.le
    have hsmall : tQuery31 G D₀ ≤ 40 * 4 ^ G.m₀ + 40 := by
      unfold tQuery31 tIpAt <;> simp_all
    exact_mod_cast hsmall
  · have hquery : (tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) : ℝ)
        ≤ K * G.queryCost D₀ :=
      hK (parOf G N D₀) (switchOf31 G D₀) (hHyp hm)
    have htime :
        tQuery31 G D₀ = tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) + 20 := by
      unfold tQuery31 <;> simp_all
    have h40 : (20 : ℝ) ≤ ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [htime]
    push_cast at h40 ⊢
    linarith

end

end Light.Sec4
