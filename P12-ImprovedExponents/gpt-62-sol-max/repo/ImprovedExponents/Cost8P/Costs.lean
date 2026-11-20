module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ImprovedExponents.Cost8P.Within
public import ImprovedExponents.PrunedProgram.Wrapper.Times

@[expose] public section

/-! Bounds for preprocessing with pruned encodings and for the complete offline routine. -/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4

/-- The cost `cost8P` of the pruned preprocessing of Theorem 30 at the parameters `G`. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (preCostX)
noncomputable abbrev preCostP (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N

/-- Setting up takes O(L + N 4^m) steps. -/
private theorem exists_tPre31P_le_setup (G : RatParams) : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
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
  have hcopy : D₀ * N ≤ N * F := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hDF
  have hfill : (F - D₀) * N ≤ N * F := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hqL : G.q * m ≤ G.q * L := Nat.mul_le_mul_left _ hmL
  lia

/-- From the threshold on the pruned preprocessing takes `O(cost8P)` steps. -/
-- adapted from ImprovedExponents/Cost8X/Costs.lean (exists_tPre31_le_cost8X)
theorem exists_tPre31P_le_cost8P (G : RatParams) (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → (tPre31P c0 G N D₀ : ℝ) ≤ K * preCostP G N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31P_le_setup (G := G)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c0
  refine ⟨k * 4 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcore : (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostP G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostP G N D₀ := N_mul_pow_le_cost8P h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ preCostP G N D₀ := N_mul_le_cost8P h
  have hsetup : (tPre31P c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 4 times `cost8P`
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  nlinarith

end ImprovedExponents
