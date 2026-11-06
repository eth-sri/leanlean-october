module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ImprovedExponents.Cost8P.Within
public import ImprovedExponents.PrunedProgram.Wrapper.Times

@[expose] public section

/-!
# The costs of the pruned programs with rational parameters, against `cost8P`

`ImprovedExponents.Cost8X.Costs` bounds the time of upstream's offline routine by a constant times
`tp + w tq` for all bounds `tp`, `tq` that dominate `cost8X` and the cost of a query
(`exists_tOffline32_leX`, hypothesis `CostsWithinX`). This file has the same statement for the
pruned offline routine, whose time functions `tPre31P`, `tOffline32P` have the time `tPreCoreP` of
the pruned preprocessing, against `cost8P`: `CostsWithinP` and `exists_tOffline32P_le`.

The proofs are adapted from upstream `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean`
(Apache-2.0) and from `ImprovedExponents/Cost8X/Costs.lean`. The time of a query does not involve
the cost of the preprocessing and is taken from upstream (`CostsWithinP.toCostsWithin`); the
set-up before the preprocessing is upstream's (`exists_tPre31P_le_setup`).
-/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4

/-- The cost `cost8P` of the pruned preprocessing of Theorem 30 at the parameters `G`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (preCostX)
noncomputable abbrev preCostP G N D₀ :=
  cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N

/-- **The two bounds dominate the two costs**, at the sizes `N` and `D`, with `cost8P` in the
place of the expression (8): sizes and bounds are at least 1, `D ≤ N`, and from the threshold on
the hypotheses of Theorem 30 hold and `cost8P` and `L ∑ α_d` are at most `C tp` and `C tq`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX)
structure CostsWithinP (G : RatParams) (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  /-- The size is at least 1. -/
  one_le_N : 1 ≤ N
  /-- The bound on the preprocessing is at least 1. -/
  one_le_pre : 1 ≤ tp
  /-- The bound on a query is at least 1. -/
  one_le_query : 1 ≤ tq
  /-- From the threshold on: the hypotheses of Theorem 30 and the two costs. -/
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G : RatParams}

/-- For `m ≥ m₀` the cost `cost8P` is at most `C tp`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.pre_le)
def CostsWithinP.pre_le {C} {N D₀} {tp tq} (h : CostsWithinP G C N D₀ tp tq)
     hm :=
  (h.above hm).2.1

/-- The bound on a query, as upstream wants it: the expression (8) is dominated by itself. This
gives upstream's facts about queries, which do not involve (8). -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.toCostsWithin)
theorem CostsWithinP.toCostsWithin {C} {N D₀} {tp tq}
    (h : CostsWithinP G C N D₀ tp tq) :
    CostsWithin G (max C 1) N D₀ (max 1 G.preCost N D₀) tq := by
  refine ⟨h.one_le_query, fun hm =>
    ⟨(by ram_arith : G.Hyp N D₀), ?_, ((by ram_arith : costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq)).trans ?_⟩⟩
  · exact (le_max_right 1 _).trans (le_mul_of_one_le_left (by positivity) (le_max_right C 1))
  · exact mul_le_mul_of_nonneg_right (le_max_left C 1) (zero_le_one.trans h.one_le_query)

/-- From the threshold on, `tPre31P` and `tPre31` differ only in the time of the core. -/
theorem tPre31P_add_tPreCore c0 N D₀ (hm : G.m₀ ≤ logFour D₀) :
    tPre31P c0 G N D₀ + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀)
      = tPre31 c0 G N D₀ + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  grind [tPre31P, tPre31]

/-- Setting up takes `O(L + N 4^m)` steps: upstream's `exists_tPre31_le_setup` for the pruned
preprocessing. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean
-- (exists_tPre31_le_setup)
theorem exists_tPre31P_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31P c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  refine ⟨k, fun c0 N D₀ hm => ?_⟩
  have  := hk c0 N D₀ hm
  have  := tPre31P_add_tPreCore (G := G) c0 N D₀ hm
  omega

/-- From the threshold on the pruned preprocessing takes `O(cost8P)` steps. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_le_cost8X)
theorem exists_tPre31P_le_cost8P G c0 : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → tPre31P c0 G N D₀ ≤ K * preCostP G N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31P_le_setup (G := G)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c0
  refine ⟨k * 4 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩

  have  : (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostP G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have  : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostP G N D₀ := N_mul_pow_le_cost8P h
  have  : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ preCostP G N D₀ := N_mul_le_cost8P h
  have  : (tPre31P c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 4 times `cost8P`
  have  : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) (mod_cast hN)
  have  : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have  : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (4 * preCostP G N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The time of the pruned preprocessing** is at most a constant times every bound `tp ≥ 1`
that, from the threshold on, dominates `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_leX)
theorem exists_tPre31P_le G {C} (hC : 0 ≤ C) c0 : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithinP G C N D₀ tp tq → tPre31P c0 G N D₀ ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31P_le_cost8P G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := (20 * G.m₀ + 50 : ℕ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31P c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      grind [tPre31P, tLog4]
    exact_mod_cast hsmall
  · ram_safe

/-- **The time of the pruned offline routine**, with `k` further steps, is at most a constant
times `tp + w tq`, for all bounds `tp, tq ≥ 1` that dominate `cost8P` and the cost of a query. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tOffline32_leX)
theorem exists_tOffline32P_le G {C} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithinP G C N D₀ tp tq →
      tOffline32P c0 G N D₀ w + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31P_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G (hC.trans (le_max_left C 1))
  refine ⟨Ap + 20 + k + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have  := hAp h
  have  := hAq h.toCostsWithin
  have  := h.one_le_pre
  have  := h.one_le_query

  have  := mul_nonneg (by positivity : (0 : ℝ) ≤ (w : ℝ)) (by linarith)
  have  : (tOffline32P c0 G N D₀ w : ℝ)
      = (tPre31P c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp_all [tOffline32P]
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  nlinarith

end ImprovedExponents
