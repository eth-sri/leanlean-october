module
public import QPBT.Combining.ExtendedLines.Overlap

/-! # The paired subline overlap estimate

Compare the completed point-pair measurement with the ordered product using the
uniform *joint* point marginal. Removing the X projection from that product
costs the square root of the X deficit. The two individual deficits use only
the one-point marginal mixtures of `SubLineOverlap`.
-/
@[expose] public section
namespace MIPStarRE.QPBT
open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section
variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ} (sublines : SubLineWitness P)
  (lines : CombinedLinesWitness S points δP) (first second : Placement)

set_option maxHeartbeats 1000000 in
theorem SubLineWitness.paired_deficit (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (pairedSublineOverlap S points lines first second) ≤
      6 * (δQ ^ (1 / 2 : ℝ) + Real.sqrt P.m *
        (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) + ε ^ (1 / 4 : ℝ))) := by
  let E := S.componentEffect second.side
  let ordered xz o := E .Z xz o * E .X xz o
  let joint xz := (points.completed second.side xz).effect
  let mean := sublines.meanOverlap lines first second
  let A (w : LinePointPairSample P) := S.placedMeasurement first (lines.evaluated first.side w)
  let placed (R : PauliPoint P × PauliPoint P → EvaluatedPair P → Op (S.ExpandedLocalSpace second.side))
      (w : LinePointPairSample P) (o : EvaluatedPair P) := S.place second (R w.coords o)
  have hdist : opFamilyDistSq sublines.evalLaw (placed joint) (placed ordered) S.psiHat ≤ 4 * δQ := by
    unfold opFamilyDistSq
    dsimp only [placed, joint, ordered, E]
    erw [avgOver_congr sublines.evalLaw _ _ fun w => S.completedPair_norm_sq_sum points second .Z w.coords]
    simp only [PauliKind.component, PauliKind.other]
    exact (sublines.avg_coords _).le.trans (points.orderedZX_dist_le second)
  have hgap : |mean joint - mean ordered| ≤ Real.sqrt (4 * δQ) :=
    abs_overlap_gap_le_sqrt_of_opFamilyDistSq sublines.evalLaw A (placed joint) (placed ordered) S.psiHat sublines.evalLaw_isProbability S.psiHat_norm hdist
  have hproj (W : PauliKind) (w : LinePointPairSample P) (o : EvaluatedPair P) : IsProj (placed (E W) w o) :=
    S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _)
  have hcomm (W : PauliKind) (w : LinePointPairSample P) (o : EvaluatedPair P) :
      Commute ((A w).effect o) (placed (E W) w o) := S.place_comm _ _ hopposite _ _
  have hcs : |mean ordered - mean (E .Z)| ≤ Real.sqrt (1 - mean (E .X)) :=
    abs_overlap_gap_le_sqrt_one_sub_of_isProj' (A := A) (B := placed (E .X)) (C := placed (E .Z))
      sublines.evalLaw (placed ordered) S.psiHat sublines.evalLaw_isProbability S.psiHat_norm
      (hproj .X) (hproj .Z) (hcomm .X) (hcomm .Z) (fun w o => S.place_mul second _ _)
  have hP : 0 ≤ δP := (avgOver_nonneg _ _ fun s =>
    consistencyDefect_integrand_nonneg S first second hopposite _ _).trans (lines.consistent first second hopposite)
  have hQ := (opFamilyDistSq_nonneg _ _ _ _).trans (points.self_consistent first second hopposite)
  have hroot (W : PauliKind) : Real.sqrt (1 - mean (E W)) ≤
      2 * Real.sqrt P.m * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) :=
    (Real.sqrt_le_sqrt (sublines.component_deficit lines first second hopposite W)).trans
      (sqrt_deficit_bound_le _ _ _ (by exact_mod_cast P.one_le_m) hP hQ)
  have hz : 0 ≤ mean (E .Z) := avgOver_nonneg _ _ fun w => Finset.sum_nonneg fun o _ =>
    stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      ((lines.evaluated first.side w).pos o) (S.pointMeasExpOption_isProj _ _ _ _).nonneg)
  have hz' : 1 - mean (E .Z) ≤ Real.sqrt (1 - mean (E .Z)) := by
    by_cases h : 0 ≤ 1 - mean (E .Z)
    · exact Real.le_sqrt_of_sq_le (by nlinarith)
    · exact (le_of_not_ge h).trans (Real.sqrt_nonneg _)
  rw [← sublines.mean_completed lines first second]
  change 1 - mean joint ≤ _
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_eq_rpow δQ] at hgap
  norm_num at hgap
  have hhalf := Real.rpow_nonneg hQ (1 / 2 : ℝ)
  have hε := mul_nonneg (Real.sqrt_nonneg P.m) (rpow_quarter_nonneg ε)
  have hsum := mul_nonneg (Real.sqrt_nonneg P.m) (add_nonneg (rpow_quarter_nonneg δP) (rpow_quarter_nonneg δQ))
  simp only [Real.rpow_eq_pow] at hε hsum
  linarith only [hgap, hcs, hz', hhalf, hε, hsum, neg_le_abs (mean joint - mean ordered), neg_le_abs (mean ordered - mean (E .Z)),
    hroot .Z, hroot .X]

end
end MIPStarRE.QPBT
