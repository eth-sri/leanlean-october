/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Limits
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline
public import ThreeSumApsp.TacticsShort

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

open ThreeSumApsp

section
variable (G : RatParams)

/-- **The two bounds dominate the two costs**, at the sizes N and D: sizes and bounds are at least
1, D ≤ N, and from the threshold on the hypotheses of Theorem 30 hold and its two cost expressions,
(8) and L ∑ α_d, are at most C tp and C tq. -/
structure CostsWithin (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  one_le_N : 1 ≤ N
  one_le_D : 1 ≤ D₀
  D_le_N : D₀ ≤ N
  one_le_pre : 1 ≤ tp
  one_le_query : 1 ≤ tq
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G} in
/-- For m ≥ m₀ the hypotheses of Theorem 30 hold. -/
theorem CostsWithin.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

variable {G} in
/-- For m ≥ m₀ the cost of a query is at most C tq. -/
theorem CostsWithin.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- A quantity that is bounded below the threshold, and at most a constant times a cost from the
threshold on, is at most a constant times every bound t ≥ 1 that dominates the cost. -/
theorem exists_le_of_small_of_large {C : ℝ} (hC : 0 ≤ C) {S K : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D₀ : ℕ) (cost t z : ℝ), 1 ≤ t → (G.m₀ ≤ logFour D₀ → cost ≤ C * t) →
      (logFour D₀ < G.m₀ → z ≤ S) → (G.m₀ ≤ logFour D₀ → z ≤ K * cost + S) → z ≤ A * t := by
  refine ⟨S + K * C, by positivity, fun D₀ cost t z ht hcost hsmall hlarge => ?_⟩
  have hsplit : (S + K * C) * t = S * t + K * (C * t) := by ring
  have hSt := le_mul_of_one_le_right hS ht
  rw [hsplit]
  by_cases hm : logFour D₀ < G.m₀
  · linarith [hsmall hm, mul_nonneg hK (mul_nonneg hC (by linarith : (0 : ℝ) ≤ t))]
  · linarith [hlarge tac_omega, mul_le_mul_of_nonneg_left (hcost tac_omega) hK]

/-! ### The preprocessing -/

/-- Setting up takes O(L + N 4^m) steps. -/
theorem exists_tPre31_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31 c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) := by
  refine ⟨20 + 20 * G.b + 20 * G.q + 352, fun c0 N D₀ hm => ?_⟩
  have ham := G.am_le (logFour D₀)
  have hpm := G.pm_le (logFour D₀)
  have hmL : logFour D₀ ≤ G.L (logFour D₀) := by have := G.ten_le_L (logFour D₀); omega
  have hDF : D₀ ≤ 4 ^ logFour D₀ := le_D_logFour D₀
  unfold tPre31
  rw [if_neg (not_lt.2 hm)]
  simp only [tLog4, tCeilMul, tPadX, tCopy, tFill, D]
  generalize G.L (logFour D₀) = L at *
  generalize logFour D₀ = m at *
  generalize 4 ^ m = F at *
  have hcopy : D₀ * N ≤ N * F := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hDF
  have hfill : (F - D₀) * N ≤ N * F := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hqL : G.q * m ≤ G.q * L := Nat.mul_le_mul_left _ hmL
  have hpad : N * (16 * F + 80) = 16 * (N * F) + 80 * N := by ring
  have hk : (20 + 20 * G.b + 20 * G.q + 352) * (L + 1 + N * F + N)
      = 20 * L + 20 * (G.b * L) + 20 * (G.q * L) + (20 + 20 * G.b + 20 * G.q) * (1 + N * F + N)
        + 352 * (L + 1 + N * F + N) := by ring
  omega

/-! ### A query -/

/-- **The time of a query** is at most a constant times every bound tq ≥ 1 that, from the threshold
on, dominates the cost L ∑ α_d of Theorem 30. -/
theorem exists_tQuery31_le {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq → (tQuery31 G D₀ : ℝ) ≤ A * tq := by
  obtain ⟨K, hK0, hK⟩ := exists_tQueryAt_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ)) tac_positivity hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tq _ h.one_le_query h.query_le (fun hm => ?_) fun hm => ?_⟩
  · -- an inner product of D ≤ 4^m₀ summands
    have hD := (Nat.clog_le_iff_le_pow tac_norm_num).1 hm.le
    have hsmall : tQuery31 G D₀ ≤ 40 * 4 ^ G.m₀ + 40 := by
      unfold tQuery31 tIpAt
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have hquery : (tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) : ℝ)
        ≤ K * G.queryCost D₀ :=
      hK (parOf G N D₀) (switchOf31 G D₀) (h.hyp hm)
    have htime :
        tQuery31 G D₀ = tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) + 20 := by
      unfold tQuery31
      rw [if_neg (not_lt.2 hm)]
    have h40 : (20 : ℝ) ≤ ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ) := by exact_mod_cast tac_omega
    rw [htime]
    push_cast at h40 ⊢
    linarith

end

/-! ### Space and the nesting of calls -/

end Light.Sec4