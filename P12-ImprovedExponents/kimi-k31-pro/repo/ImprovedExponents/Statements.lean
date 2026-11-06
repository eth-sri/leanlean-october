module

public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.Pipeline.General
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Optimum.NumValues
public import ImprovedExponents.AllEdges.Pairs.TimeBound
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Real

/-- **With pruned encodings** (`c = 22`): a saving of more than `0.002095` for Exact Triangle. -/
theorem allSolved_pruned_num : ∃ δ : ℝ, (0.002095 : ℝ) < δ ∧ AllSolved δ :=
  ⟨(0.002095 + savingF (basePruned 22) (Gam 22)) / 2, by linarith [savingF_pruned_gt],
    allSolved_pruned (c := 22) (by norm_num) (by linarith [savingF_pruned_gt])
      (by linarith [savingF_pruned_gt])⟩

/-- **The (min,+)-product and APSP with pruned encodings**, with the whole saving. -/
theorem minPlusSolved_pruned {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllEdges.MinPlusSolved δ := by
  have hhalf : savingF (basePruned c) (Gam c) ≤ 1 / 2 :=
    savingF_le_half (basePruned_pos (by linarith)).le (Gam_pos (by linarith)).le
  exact AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    (by linarith)
    (explicitFrom_pruned hc hδ0 hδ AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)

/-- **3SUM in `O(n^1.99896)` steps on the word RAM.** -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_pruned_num
  exact SolvedInTime.endStatement (h.2 _ (by norm_num; linarith)) rfl (by norm_num)

/-- **Exact Triangle in `O(n^2.99791)` steps on the word RAM.** -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_pruned_num
  exact SolvedInTime.endStatement (h.1 _ (by norm_num; linarith)) rfl (by norm_num)

/-- **The (min,+)-product in `O(n^2.99791)` steps on the word RAM.** -/
theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  SolvedInTime.endStatement
    ((minPlusSolved_pruned (c := 22) (by norm_num) (by norm_num) savingF_pruned_gt).1 _
      (by norm_num)) rfl (by norm_num)

/-- **APSP in `O(n^2.99791)` steps on the word RAM.** -/
theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  SolvedInTime.endStatement
    ((minPlusSolved_pruned (c := 22) (by norm_num) (by norm_num) savingF_pruned_gt).2 _
      (by norm_num)) rfl (by norm_num)

end ImprovedExponents
