module

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

The setup and query bounds are adapted directly from upstream's
`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Costs.lean` (Apache-2.0).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-- The cost `cost8P` of the pruned preprocessing of Theorem 30 at the parameters `G`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (preCostX)
noncomputable abbrev preCostP (G : RatParams) (N D₀ : ℕ) : ℝ :=
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

/-- For `m ≥ m₀` the hypotheses of Theorem 30 hold. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.hyp)
theorem CostsWithinP.hyp {C } {N D₀ } {tp tq } (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

/-- For `m ≥ m₀` the cost `cost8P` is at most `C tp`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.pre_le)
theorem CostsWithinP.pre_le {C } {N D₀ } {tp tq } (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : preCostP G N D₀ ≤ C * tp :=
  (h.above hm).2.1

/-- For `m ≥ m₀` the cost of a query is at most `C tq`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (CostsWithinX.query_le)
theorem CostsWithinP.query_le {C } {N D₀ } {tp tq } (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- Setting up takes O(L + N 4^m) steps. -/
private theorem setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31P c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  refine ⟨20 + 20 * G.b + 20 * G.q + 352, fun c0 N D₀ hm => ?_⟩
  have ham := G.am_le (logFour D₀)
  have hpm := G.pm_le (logFour D₀)
  have hmL : logFour D₀ ≤ G.L (logFour D₀) := by have := G.ten_le_L (logFour D₀); omega
  have hDF : D₀ ≤ 4 ^ logFour D₀ := le_D_logFour D₀
  unfold tPre31P
  rw [if_neg (not_lt.2 hm)]
  simp only [tLog4, tCeilMul, tPadX, tCopy, tFill, D]
  generalize tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) = tp
  generalize G.L (logFour D₀) = L at *
  generalize logFour D₀ = m at *
  generalize 4 ^ m = F at *
  have hcopy : D₀ * N ≤ N * F := by nlinarith
  have hfill : (F - D₀) * N ≤ N * F := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hqL : G.q * m ≤ G.q * L := Nat.mul_le_mul_left _ hmL
  grind

/-- **The time of a query** is at most a constant times every bound tq ≥ 1 that, from the threshold
on, dominates the cost L ∑ α_d of Theorem 30. -/
private theorem queryTime (G : RatParams) {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithinP G C N D₀ tp tq → (tQuery31 G D₀ : ℝ) ≤ A * tq := by
  obtain ⟨K, hK0, hK⟩ := exists_tQueryAt_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tq _ h.one_le_query h.query_le (fun hm => ?_) fun hm => ?_⟩
  · -- an inner product of D ≤ 4^m₀ summands
    have hD := (Nat.clog_le_iff_le_pow (by norm_num)).1 hm.le
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
    have h40 : (20 : ℝ) ≤ ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [htime]
    push_cast at h40 ⊢
    linarith


/-- From the threshold on the pruned preprocessing takes `O(cost8P)` steps. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_le_cost8X)
theorem exists_tPre31P_le_cost8P (G : RatParams) (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → (tPre31P c0 G N D₀ : ℝ) ≤ K * preCostP G N D₀ := by
  obtain ⟨k, hk⟩ := setup (G := G)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c0
  refine ⟨k * 4 + Cp, by grind, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by simp_all
  have hcore : (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostP G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostP G N D₀ := N_mul_pow_le_cost8P h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ preCostP G N D₀ := N_mul_le_cost8P h
  have hsetup : (tPre31P c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 4 times `cost8P`
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by grind) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by simp) (by linarith)
  have hsum : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (4 * preCostP G N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by simp)
  linarith

/-- **The time of the pruned preprocessing** is at most a constant times every bound `tp ≥ 1`
that, from the threshold on, dominates `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_leX)
theorem exists_tPre31P_le (G : RatParams) {C } (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ } {tp tq }, CostsWithinP G C N D₀ tp tq → (tPre31P c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31P_le_cost8P G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by grind) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31P c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      grind [tPre31P, tLog4]
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    grind

/-- **The time of the pruned offline routine**, with `k` further steps, is at most a constant
times `tp + w tq`, for all bounds `tp, tq ≥ 1` that dominate `cost8P` and the cost of a query. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tOffline32_leX)
theorem exists_tOffline32P_le (G : RatParams) {C } (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ } {tp tq } (w : ℕ), CostsWithinP G C N D₀ tp tq →
      (tOffline32P c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31P_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := queryTime G hC
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have hpre := hAp h
  have hquery := hAq h
  have htp := h.one_le_pre
  have htq := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by simp
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32P c0 G N D₀ w : ℝ)
      = (tPre31P c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp [tOffline32P]
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  have hfirst : (tPre31P c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
    linarith [le_mul_of_one_le_right (by grind : (0 : ℝ) ≤ 20 + (k : ℝ)) htp]
  have hsecond : (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (Aq + 30) * ((w : ℝ) * tq) := by
    calc (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (w : ℝ) * ((Aq + 30) * tq) :=
          mul_le_mul_of_nonneg_left (by linarith) hw
      _ = (Aq + 30) * ((w : ℝ) * tq) := by ring
  have hcross₁ : 0 ≤ (Ap + 20 + k) * ((w : ℝ) * tq) := mul_nonneg (by grind) hwtq
  have hcross₂ : 0 ≤ (Aq + 30) * tp := mul_nonneg (by grind) (by linarith)
  grind

end ImprovedExponents
