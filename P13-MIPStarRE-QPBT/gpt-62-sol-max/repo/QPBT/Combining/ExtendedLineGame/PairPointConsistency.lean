module

public import QPBT.Combining.ExtendedLineGame.RetainedPointMass
public import QPBT.Combining.OverlapGap

/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

/-- The retained diagonal overlap with the actual opposite point measurement. -/
def retainedPointOverlap {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) : ℝ :=
  avgOver (uniformDistribution (PauliPoint P)) (fun x =>
    ∑ pair : PolyPair P, S.placedCorrelation p1 p2
      (R.effect (directCombinedEmbedding P pair)) ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)))

private theorem retained_mass_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side))
    (hR : Measurement.IsProjective R) :
    (∑ pair : PolyPair P,
      ‖applyOperatorToState (S.place p (R.effect (directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2) = 1 - separatedPolynomialMass S p R := by
  classical
  let w := fun g => ‖polyOutcomeState S p R g‖ ^ 2
  change ∑ pair : PolyPair P, w (directCombinedEmbedding P pair) = _
  rw [← sum_filter_range_embedding (directCombinedEmbedding P) w]
  exact eq_sub_of_add_eq ((Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun g => g ∈ Set.range (directCombinedEmbedding P)) w).trans (polyOutcomeState_norm_sum S p R hR))

/-- Retained mass splits exactly into point overlap and point mismatch.
This is the normalized good/bad identity of `eq:qld-s-good-and-bad`; the
individual projected vectors in its proof remain unnormalized. -/
theorem retainedPointMismatch_eq {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (W : PauliKind) :
    retainedPointMismatch S p1 p2 R W =
      1 - separatedPolynomialMass S p1 R - retainedPointOverlap S p1 p2 R W := by
  have hpoint (x : PauliPoint P) (pair : PolyPair P) :
      ‖applyOperatorToState
        (1 - S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)))
        (applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
          S.psiHat)‖ ^ 2 =
      ‖applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2 - S.placedCorrelation p1 p2
          (R.effect (directCombinedEmbedding P pair)) ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)) := by
    have hM := S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ W x)
      (evalAt W x pair)
    have hG := S.placedMeasurement_isProjective p1 R hR (directCombinedEmbedding P pair)
    simp only [ProjectiveSetting.placedMeasurement_effect] at hM hG
    have hcomm := S.place_comm p1 p2 hopposite
      (R.effect (directCombinedEmbedding P pair))
      ((S.pointMeasExp p2.side W x).effect (evalAt W x pair))
    rw [norm_applyOperatorToState_sq]
    change stateQForm _ _ = _
    rw [hM.one_sub.isSelfAdjoint.isHermitian.eq, hM.one_sub.isIdempotentElem.eq,
      stateQForm_sub, stateQForm_one,
      stateQForm_applyOperatorToState_eq_of_isProj S.psiHat hG hcomm.symm, ← hcomm]
  unfold retainedPointMismatch retainedPointOverlap
  simp_rw [hpoint, Finset.sum_sub_distrib, avgOver_sub, avgOver_uniform_const]
  rw [retained_mass_eq S p1 R hR]

/-- Completion increases the retained diagonal overlap on any opposite
placement. This transports the completion estimate to all four directed
expanded placements, without identifying the player spaces. -/
theorem directPairMeasurement_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) (W : PauliKind) :
    S.placedDefect p1 p2
      (uniformDistribution (PauliPoint P)) (fun x => (directPairMeasurement R pair₀).postprocess
        (evalAt W x)) (S.pointMeasExp p2.side W) ≤
      separatedPolynomialMass S p1 R + retainedPointMismatch S p1 p2 R W := by
  classical
  have hcancel (a b : ℝ) : a + (1 - a - b) = 1 - b := by ring
  rw [S.placedDefect_eq_one_sub _ _ _ _ _ (uniformDistribution_isProbability _),
    retainedPointMismatch_eq S p1 p2 hopposite R hR W, hcancel]
  apply sub_le_sub_left
  unfold retainedPointOverlap
  simp_rw [S.placed_overlap_postprocess]
  exact avgOver_mono _ _ _ fun x => Finset.sum_le_sum fun pair _ =>
    S.placedCorrelation_mono_left p1 p2 hopposite (directPairMeasurement_effect_le R pair₀ pair)
      ((S.pointMeasExp p2.side W x).pos (evalAt W x pair))

/-- The completed pair measurement has point defect at most bad mass plus
`2E + 4/q`, for each basis and every opposite placement. -/
theorem directPairMeasurement_consistency_le_ordered_error
    {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (pair₀ : PolyPair P) (W : PauliKind) :
    S.placedDefect p1 p2
      (uniformDistribution (PauliPoint P)) (fun x => (directPairMeasurement R pair₀).postprocess
        (evalAt W x)) (S.pointMeasExp p2.side W) ≤
      separatedPolynomialMass S p1 R +
        2 * extendedPolynomialOrderedError S p1 p2 R W + 4 / P.q := by
  have h := directPairMeasurement_consistency_le S p1 p2 hopposite R hR pair₀ W
  have hm := retainedPointMismatch_le_ordered_error S p1 p2 hopposite R hR W
  linarith

/-- Construct complete projective polynomial-pair measurements with all four
point-consistency conclusions at the actual explicit error. The point and
directly indexed completed-answer line witnesses are exactly the inputs of
the established rounded constructor. They are not assumptions of the source
theorem; its proof supplies them internally and absorbs the eighth-root rounding term.
The direct-domain and line-error discrepancies remain documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/
theorem pair_witness_of_points_lines_explicit :
    ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := P.extendedLdError pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower δQ δL
      Nonempty (GlobalPairWitness S (P.pairError δQ delta)) := by
  intro P ε δQ δL S points lines delta
  let eta := roundedLdError delta
  obtain ⟨w, hmass⟩ := rounded_polynomial_separated_mass_explicit P ε δQ δL S points lines
  let pair₀ : PolyPair P := (0, 0)
  have hbound :
      6 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) +
        2 * (4 * eta + 8 * δQ) + 4 / P.q =
      P.pairError δQ delta := by
    change _ = 8 * (4 * eta + 8 * δQ) + _
    push_cast
    ring
  refine ⟨fun side => directPairMeasurement (w.measure side) pair₀,
    fun side => directPairMeasurement_projective _ pair₀ (w.projective side), ?_⟩
  intro p hp W
  rw [← hbound]
  refine (directPairMeasurement_consistency_le_ordered_error S p _ p.opposite_partner
    (w.measure p.side) (w.projective p.side) pair₀ W).trans ?_
  gcongr
  · exact hmass hp
  · exact w.ordered hp W

end

end MIPStarRE.QPBT.ExtendedLineGame
