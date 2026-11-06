module

public import Mathlib.Tactic
public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Optimum.NumLog
public import ImprovedExponents.AllEdges.Pairs.TimeBound
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section
namespace ImprovedExponents
open ThreeSumApsp ThreeSumApsp.WordRam Light Real

set_option maxHeartbeats 0 in
/-- A concrete rational choice of all algorithmic parameters, shared by both hosts. -/
theorem numeric_explicit (M : DetTimeModel) (hM : M.lopDetect = lightModel.lopDetect)
    (hhost : MidHostRat M) : ExplicitFrom M 0.002091 1 := by
  have  : (25.10483 : ℝ) ≤ basePruned 22 := le_basePruned 4
  have  : basePruned 22 ≤ (25.10485 : ℝ) := basePruned_le 4
  have  : (1.38629 : ℝ) ≤ log 4 := by
    refine le_trans ?_ logFour_mem.1
    numlog
  have  : (0.076207 : ℝ) ≤ gammaX 22 0.116036 := le_gammaX 4
  have  : qOf 0.116036 ≤ 0.44285 := qOf_le (-3)
  have hR : (0.0549 : ℝ) < RcP 22 0.0762 := by
    unfold RcP thinR
    rw [lt_div_iff₀ (by nlinarith : 0 < basePruned 22 + 0.0762 * log 4)]
    nlinarith

  refine explicitFrom_of_thinClaim_mid (σ := 0.51905) (e := 0.05489) (by
    have h := thinClaimP_gammaX (a := 22) (b := 1) (p := 29009) (q := 250000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r := 453) (s := 25) (by norm_num) (by norm_num) (by norm_num; nlinarith)
      (γ := 0.0762) (ε := 0.0549) (by norm_num) (by norm_num; linarith)
      (by norm_num at hR ⊢; exact hR) (by norm_num)
    convert h using 1 <;> norm_num
   : ThinClaim lightModel 0.0549 0.0762 (qOf 0.116036)) (by norm_num)
    (qOf_nonneg _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ M hM hhost
  rw [min_eq_left (by norm_num; linarith : (0.0762 : ℝ) ≤ (0.51905 : ℚ) - qOf 0.116036)]
  norm_num


/-- Convert the two running-time bounds to the trusted word-RAM statements. -/
theorem AllSolved.endStatements {δ : ℝ} (h : AllSolved δ) {r₃ rE : ℚ}
    (h₃ : 2 - δ / 2 < (r₃ : ℝ)) (hE : 3 - δ < (rE : ℝ))
    (h₃0 : 0 ≤ r₃) (hE0 : 0 ≤ rE) :
    EndStatement.ThreeSum.SolvedInTime r₃ ∧ EndStatement.ExactTriangle.SolvedInTime rE :=
  ⟨SolvedInTime.endStatement (h.threeSum _ h₃) rfl h₃0,
    SolvedInTime.endStatement (h.exactTriangle _ hE) rfl hE0⟩

theorem endStatements_pruned :
    EndStatement.ThreeSum.SolvedInTime 1.99896 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  (allSolved_of_explicitFrom (by norm_num) (by norm_num)
    (numeric_explicit lightModel rfl midHostRat_light)).endStatements
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- 3SUM in `O(n^1.99896)` word-RAM steps. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 :=
  endStatements_pruned.1

/-- Exact Triangle in `O(n^2.99791)` word-RAM steps. -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  endStatements_pruned.2

theorem AllEdges.MinPlusSolved.endStatements {δ : ℝ} (h : AllEdges.MinPlusSolved δ) {rM : ℚ}
    (hM : 3 - δ < (rM : ℝ)) (hM0 : 0 ≤ rM) :
    EndStatement.MinPlusProduct.SolvedInTime rM ∧ EndStatement.APSP.SolvedInTime rM :=
  ⟨SolvedInTime.endStatement (h.minPlus _ hM) rfl hM0,
    SolvedInTime.endStatement (h.apsp _ hM) rfl hM0⟩

theorem endStatements_allEdges_pruned :
    EndStatement.MinPlusProduct.SolvedInTime 2.99791 ∧ EndStatement.APSP.SolvedInTime 2.99791 :=
  (AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    (by norm_num) (numeric_explicit AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)).endStatements
      (by norm_num) (by norm_num)

/-- The (min,+)-product in `O(n^2.99791)` word-RAM steps. -/
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.1

/-- APSP in `O(n^2.99791)` word-RAM steps. -/
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.2

end ImprovedExponents
