module

public import Mathlib.Tactic
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# From Exact Triangle to the four problems, on the word RAM

`AllSolved δ` collects what a saving `δ` for Exact Triangle gives, as statements about programs of
upstream's word RAM (`ThreeSumApsp.WordRam.SolvedInTime Q a 0`: for every exponent `κ` of the
bound on the numbers there is a program that solves `Q` in `O(n^a)` steps):

* Exact Triangle in `O(n^a)` for every `a > 3 - δ`;
* 3SUM in `O(n^a)` for every `a > 2 - δ/2` (Theorem 21(a) of the paper);
* the (min,+)-product and APSP in `O(n^a)` for every `a > 3 - δ/3` (Theorem 21(b)).

`allSolved_of_uniform` derives it from the claim `Claim.ExactTriangleUniform lightModel δ e`
together with an explicit bound from some size on; all the work is upstream's
(`Light.Sec3.threeSum_of_uniform`, `minPlus_polylog_of_uniform`, `apsp_polylog_of_uniform`, and the
compiler to the word RAM).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec3

/-- What a saving `δ` for Exact Triangle gives for the four problems, on the word RAM. -/
structure AllSolved (δ : ℝ) : Prop where
  /-- Exact Triangle in `O(n^a)` steps for every `a > 3 - δ`. -/
  exactTriangle : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.ExactTriangle a 0
  /-- 3SUM in `O(n^a)` steps for every `a > 2 - δ/2`. -/
  threeSum : ∀ a : ℝ, 2 - δ / 2 < a → SolvedInTime EndStatement.ThreeSum a 0
/-- Exact Triangle in `O(n^a)` steps of the word RAM for every `a > 3 - δ`, from the explicit
bound `K κ n^{3-δ} (log n)^e` from some size on. -/
theorem exactTriangle_of_explicitFrom {δ} {e} (h : ExplicitFrom lightModel δ e) {a}
    (ha : 3 - δ < a) : SolvedInTime EndStatement.ExactTriangle a 0 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  refine FromClaims.solvedInTime_of_claim realized_exactTriangle fun κ _ =>
    ⟨T, hT, UpperPowPolylog.upperBigOPow ⟨K * max κ 1, e, ?_⟩ ha⟩
  filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn

  have h := hb n (max κ 1) ((n : ℝ) ^ κ) (le_trans (le_max_left _ _) hn) (le_max_right _ _)
    (Real.rpow_le_rpow_of_exponent_le (by simp_all) (le_max_left _ _))
  calc T n (n ^ κ) ≤ K * (max κ 1 * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) := h
    _ = K * max κ 1 * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) := by ring

/-- **From Exact Triangle to the four problems.** -/
theorem allSolved_of_uniform {δ} {e} (hδ1 : δ ≤ 1) (hex : ExplicitFrom lightModel δ e)
    (hu : Claim.ExactTriangleUniform lightModel δ e) : AllSolved δ :=
  ⟨fun _ ha => exactTriangle_of_explicitFrom hex ha,
    fun _ ha => threeSum_of_uniform hδ1 hu ha⟩

end ImprovedExponents
