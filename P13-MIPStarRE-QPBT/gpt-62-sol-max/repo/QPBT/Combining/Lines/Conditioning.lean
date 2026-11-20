module

public import QPBT.Combining.Lines.PointComparison
public import QPBT.Combining.Lines.CombinedMeasurement
public import QPBT.Combining.Lines.ConsistencyPositivity
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.Sandwich.Support
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore
public import QPBT.Games.ErrorFunctions
public import QPBT.Combining.Lines.ConditionalCollision
public import QPBT.Combining.Lines.NondegeneratePastingMass
public import QPBT.Combining.Lines.DiscardedMass

/-!
# Conditioning the line-pasting distribution

The proof conditions only on nonzero X directions. Conditional collision
bounds apply there, and the discarded probability is restored explicitly.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- For arbitrary complete measurements on opposite placements, conditioning
and question relabeling inflate the defect by at most the inverse retained mass.
The needed nonnegativity follows from positivity on opposite registers, not a
new input. Formalization-only support for `eq:pasting-q1`, paper lines 936--963. -/
theorem consistencyDefect_nondegenerateLinePastingDist_le {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams)) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams)) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    S.placedDefect p1 p2
      (nondegenerateLinePastingDist P.toLdParams) (fun question => first (question.2, question.1.2)) (fun question => second (question.2, question.1.2)) ≤
    S.placedDefect p1 p2 (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams)) first second /
      nondegenerateLinePastingMass P.toLdParams := by
  unfold ProjectiveSetting.placedDefect measurementDefect consistencyDefect nondegenerateLinePastingDist
  rw [Distribution.avgOver_map]
  exact avgOver_restrict_le_div_mass _ _ _ _ (fun sample =>
    consistencyDefect_integrand_nonneg S p1 p2 hopp (first sample) (second sample))

/-- The supplied completed point marginals, with answers ordered Z then X,
satisfy both conditioned line comparisons with error
`(8 * δQ + 2080 * (ε + deltaLine ε)) / r`. The line families depend only on
the common line-pair question. This proves the marginal inputs in the source
order for the X-outer sandwich, rather than assuming them or omitting the point
error. Source: `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-963`. Tensor-register transport
to the bipartite pasting theorem remains separate. -/
theorem combined_points_conditioned_line_marginal_defect_le_explicit
    (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
        S.placedDefect p1 p2
          (nondegenerateLinePastingDist P.toLdParams) (fun question => ((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst) (fun question => S.lineEvalMeasExp p2.side .Z question.1.1.2 question.1.2.2) ≤ (8 * δQ + 2080 * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams ∧
        S.placedDefect p1 p2
          (nondegenerateLinePastingDist P.toLdParams) (fun question => ((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd) (fun question => S.lineEvalMeasExp p2.side .X question.1.1.1 question.2.2) ≤ (8 * δQ + 2080 * (ε + deltaLine ε)) /
            nondegenerateLinePastingMass P.toLdParams := by
  classical
  have hmass := (prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le
  have h (W : PauliKind) :=
    (consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun ab => some (W.component ab)))
      (fun sample => S.lineEvalMeasExp p2.side W (W.component sample).1 (W.component sample).2)).trans
        (div_le_div_of_nonneg_right
          (combined_points_line_marginal_defect_le_explicit P ε δQ S points p1 p2 hopp W) hmass)
  have hz := h .Z
  have hx := h .X
  unfold ProjectiveSetting.placedDefect measurementDefect consistencyDefect nondegenerateLinePastingDist at hz hx ⊢
  simp only [Distribution.avgOver_map, PauliKind.component, Measurement.postprocess_comp] at hz hx ⊢
  exact ⟨hz, hx⟩

set_option maxHeartbeats 800000 in
-- Transport through the mapped product distribution expands two postprocessed families.
/-- Restore the unconditioned consistency defect with its retained-mass factor
and additive cost at most `1/(2q)`. This holds for the supplied measurement
families on every directed opposite placement, without a defect hypothesis.
Formalization-only support for `lem:qld-xz-lines`, paper lines 950--963. -/
theorem consistencyDefect_le_nondegenerateLinePastingDist_add_mass
    {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : ((LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams)) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams)) →
      MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    S.placedDefect p1 p2 (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams)) first second ≤
    nondegenerateLinePastingMass P.toLdParams *
      S.placedDefect p1 p2
        (nondegenerateLinePastingDist P.toLdParams) (fun question => first (question.2, question.1.2)) (fun question => second (question.2, question.1.2)) + 1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
  classical
  unfold ProjectiveSetting.placedDefect measurementDefect consistencyDefect nondegenerateLinePastingDist nondegenerateLinePastingMass
  rw [Distribution.avgOver_map]
  let value := fun sample => ∑ answer : Outcome, ∑ other : Outcome,
      if answer = other then 0 else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (S.ExpandedSpace) ℂ).symm
          ((S.place p1 ((first sample).effect answer) *
            S.place p2 ((second sample).effect other)).mulVec S.psiHat))).re
  have hunit := fun sample =>
    consistencyDefect_integrand_le_one S p1 p2 hopp (first sample) (second sample)
  have h := avgOver_le_restrict_add_discarded_mass _
    (fun samples => samples.1.1.direction ≠ 0)
    (prod_linePointDist_nondegenerate_mass_pos P.toLdParams) value hunit
  have hdiscard : (∑ sample ∈ (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams)).support.filter (fun sample => ¬ sample.1.1.direction ≠ 0),
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams)).weight sample) ≤
      1 / (2 * Fintype.card (ScalarQ P.toLdParams)) := by
    rw [Distribution.sum_filter_weight_eq_avgOver]
    simpa only [ne_eq, not_not] using prod_linePointDist_zero_X_direction_mass_le P.toLdParams
  have hfinal := h.trans (add_le_add_right hdiscard _)
  exact hfinal

/-- The actual X-outer line sandwich and the supplied completed points satisfy
the mass-restoration inequality on every directed opposite placement. This is
not the final consistency estimate: its right side still contains the
conditioned defect to be bounded by one-sided pasting. Source:
`lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:942-963`;
remaining construction recorded in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem ProjectiveSetting.combinedLineMeasurement_consistency_le_conditioned
    {P : AdmissibleParams} {ε δQ : ℝ} (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    S.placedDefect p1 p2 (sourceLinePointPairDist P)
      (fun s => points.completedPair p1.side s.1.2 s.2.2)
      (pairedLineReadout (S.combinedLineMeasurement p2.side)) ≤
    nondegenerateLinePastingMass P.toLdParams *
      S.placedDefect p1 p2 (nondegenerateLinePastingDist P.toLdParams)
        (fun s => points.completedPair p1.side s.2.2 s.1.2.2)
        (fun s => pairedLineReadout (S.combinedLineMeasurement p2.side) (s.2, s.1.2)) +
      1 / (2 * Fintype.card (ScalarQ P.toLdParams)) :=
  consistencyDefect_le_nondegenerateLinePastingDist_add_mass S p1 p2 hopp _ _

end

end MIPStarRE.QPBT
