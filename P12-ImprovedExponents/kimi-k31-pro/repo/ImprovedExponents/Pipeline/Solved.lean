module

public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumPolylog
public import ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
public import ThreeSumApsp.TimeClaims.Sec3.Theorem21_22
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec3

/-- What a saving `δ` gives for Exact Triangle and 3SUM on the word RAM. -/
def AllSolved (δ : ℝ) : Prop :=
  (∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.ExactTriangle a 0) ∧
    (∀ a : ℝ, 2 - δ / 2 < a → SolvedInTime EndStatement.ThreeSum a 0)

/-- Exact Triangle from an explicit polylogarithmic bound. -/
theorem exactTriangle_of_explicitFrom {δ : ℝ} {e : ℕ} (h : ExplicitFrom lightModel δ e) {a : ℝ}
    (ha : 3 - δ < a) : SolvedInTime EndStatement.ExactTriangle a 0 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  refine FromClaims.solvedInTime_of_claim realized_exactTriangle fun κ _ =>
    ⟨T, hT, UpperPowPolylog.upperBigOPow ⟨K * max κ 1, e, ?_⟩ ha⟩
  filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have h := hb n (max κ 1) ((n : ℝ) ^ κ) (le_trans (le_max_left _ _) hn) (le_max_right _ _)
    (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _))
  calc T n ((n : ℝ) ^ κ) ≤ K * (max κ 1 * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) := h
    _ = K * max κ 1 * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) := by ring

/-- 3SUM from a uniform Exact Triangle bound. -/
theorem threeSum_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) {a : ℝ} (ha : 2 - δ / 2 < a) :
    SolvedInTime EndStatement.ThreeSum a 0 :=
  FromClaims.solvedInTime_of_claim realized_threeSum
    ((threeSum_of_uniform_theorem_21a _ e hδ hu
      (Theorem21a.of_CH20_VW13 _ ChanHe.claim_CH20_Theorem_5_1 claim_VW13_Theorem_4_3)).mono
        fun _ hf => hf.upperBigOPow ha)

/-- Exact Triangle and 3SUM from their bounds. -/
theorem allSolved_of_uniform {δ : ℝ} {e : ℕ} (hδ1 : δ ≤ 1) (hex : ExplicitFrom lightModel δ e)
    (hu : Claim.ExactTriangleUniform lightModel δ e) : AllSolved δ :=
  ⟨fun _ ha => exactTriangle_of_explicitFrom hex ha, fun _ ha => threeSum_of_uniform hδ1 hu ha⟩

end ImprovedExponents
