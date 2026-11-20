module

public import ImprovedExponents.Pipeline.ThreeSum
public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Optimum.NumLog
public import ImprovedExponents.AllEdges.Decision
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4 Real

/-- One rational certificate suffices for both hosts.  Use ratio 22, cutoff
`29/250`, thinness `.05498` and gain `.07616` in the pruned product. -/
private theorem thinCertificate : ThinClaim lightModel 0.05498 0.07616 (qOf 0.116) := by
  have hA : basePruned 22 ≤ 25.105 := basePruned_le 4
  have h4 : 1.38629 ≤ log 4 := le_trans (by numlog) logFour_mem.1
  have hpos := basePruned_pos (c := 22) (by norm_num)
  have hγ : 0.07617 ≤ gammaX 22 0.116 := le_gammaX 4
  convert thinClaimP_gammaX (a := 22) (b := 1) (p := 29) (q := 250) (r := 363) (s := 20)
      _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;>
    norm_num [RcP, thinR] <;> first | linarith | rw [lt_div_iff₀ (by linarith)]; linarith

/-- The same running-time calculation applies whether the host returns one bit or all flags. -/
private theorem certificate : ExplicitFrom AllEdges.lightModelAE 0.002091 1 := by
  have hq := qOf_nonneg (0.116 : ℝ) (by norm_num) (by norm_num)
  have hq' : qOf 0.116 ≤ 0.4428 := qOf_le (-3)
  have lop := lopClaim_of_thinClaim lightModel (by norm_num) hq (by norm_num) thinCertificate
    claim_lopCountFromThinProduct claim_lopDetectFromCount
  apply explicitFrom_mid _
    _ _ _ _ hq _ _ (fun _ => rfl) (fun _ => rfl)
    (AllEdges.midHostRat_ae 5706 100000 3668 100000 (by decide) (by decide) (by decide) (by decide))
    lop <;> norm_num
  norm_num at hq'
  simp [min_def]; split_ifs <;> linarith

private theorem decisionBound : ExplicitFrom lightModel 0.002091 1 :=
  AllEdges.decision_of_allEdges (by norm_num) certificate

/-- 3SUM on the word RAM, using the deterministic reduction to Exact Triangle. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 := by
  apply SolvedInTime.endStatement _ rfl (by norm_num)
  exact threeSum_of_explicitFrom decisionBound (by norm_num) (by norm_num)

/-- Exact Triangle on the word RAM. -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  (exactTriangle_of_explicitFrom decisionBound (by norm_num)).endStatement rfl (by norm_num)

private theorem allEdgesBound : AllEdges.MinPlusSolved 0.002091 := AllEdges.minPlusSolved_of_explicitFrom
  (by norm_num) certificate

/-- The (min,+)-product via all-edges Exact Triangle. -/
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  (allEdgesBound.minPlus _ (by norm_num)).endStatement rfl (by norm_num)

/-- APSP via the (min,+)-product. -/
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  (allEdgesBound.apsp _ (by norm_num)).endStatement rfl (by norm_num)

end ImprovedExponents
