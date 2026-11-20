module

public import ThreeSumApsp.Statements.Exponents
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ThreeSumApsp.Programs.Sec3.Theorem19.ChooseBySize
public import ImprovedExponents.Pipeline.Parameters
public import ImprovedExponents.Pipeline.Solved
public import ImprovedExponents.Total.Uniform
public import ImprovedExponents.AllEdges.Chain
public import ImprovedExponents.AllEdges.Host.ClaimAE
public import ImprovedExponents.AllEdges.Decision

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec3

private theorem explicitAE : ExplicitFrom AllEdges.lightModelAE 0.002095 1 :=
  explicitFrom22 AllEdges.lightModelAE rfl AllEdges.midHostRat_ae

private theorem explicitET : ExplicitFrom lightModel 0.002095 1 :=
  AllEdges.explicitFrom_decision (by norm_num) explicitAE

/-- 3SUM in `O(n^1.99896)` steps on the word RAM. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 := by
  have h := exactTriangleUniform_of_explicitFrom lightModel 1 (by norm_num : (0 : ℝ) ≤ 0.002095)
    (by norm_num) explicitET AllEdges.claim_bruteForce closure_chooseBySize
    (fun _ _ hle hT => SolvedIn.mono hT hle)
  exact (threeSum_of_uniform (by norm_num) h (by norm_num)).endStatement rfl (by norm_num)

/-- Exact Triangle in `O(n^2.99791)` steps on the word RAM. -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  (exactTriangle_of_explicitFrom explicitET (by norm_num)).endStatement rfl (by norm_num)

private theorem allEdgesBounds : AllEdges.MinPlusSolved 0.002095 :=
  AllEdges.minPlusSolved_of_explicitFrom (by norm_num) explicitAE

/-- The (min,+)-product in `O(n^2.99791)` steps, via all-edges Exact Triangle. -/
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  (allEdgesBounds.minPlus _ (by norm_num)).endStatement rfl (by norm_num)

/-- APSP in `O(n^2.99791)` steps on the word RAM. -/
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  (allEdgesBounds.apsp _ (by norm_num)).endStatement rfl (by norm_num)

end ImprovedExponents
