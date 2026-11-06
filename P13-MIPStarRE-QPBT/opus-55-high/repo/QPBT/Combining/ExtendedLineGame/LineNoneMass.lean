module

public import QPBT.Combining.ExtendedLineGame.EvaluatedLineComparison

/-!
# Failed completed line-evaluation mass

This module bounds the marginal Born mass of the `none` outcome of each
completed line read by the corresponding mixed line/point rejection branch.
Wrong-format point answers also read as `none`, so the proof first removes
those answer pairs using their zero Born weight and only then applies event
inclusion.

These statements concern completed `Option`-valued readouts. They do not
identify successful parameter evaluation or prove a coefficient-collision
bound.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#332.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- A direct point answer has completed read `none` exactly when its answer
tag is invalid for a point question. -/
theorem pointGameRead_eq_none_iff_invalid
    (answer : DirectLdAnswer P.extendedDirectLd) :
    pointGameRead answer = none ↔
      validDirectLdAnswer (D := P.extendedDirectLd) .point answer = false := by
  cases answer <;> simp [pointGameRead, validDirectLdAnswer]

variable (lines : ExtendedLinesWitness setting points deltaL)

/-- After zero-weight invalid point answers are removed, Alice's line-`none`
event is the event that the line read is `none` and the point read is not. -/
theorem alice_line_none_event_eq_point_some
    (kind : LdType) (sample : DirectLdSpace P.extendedDirectLd)
    (readLine : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)) :
    outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => readLine answerA = none) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB =>
          readLine answerA = none ∧ pointGameRead answerB ≠ none) := by
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hline : readLine answerA = none
  · by_cases hpoint : pointGameRead answerB = none
    · simp_all [pointGameRead_eq_none_iff_invalid, outcomeWeight_eq_zero_of_invalid, Or.inr]
    simp_all
  simp_all

/-- After zero-weight invalid point answers are removed, Bob's line-`none`
event is the event that the point read is not `none` and the line read is. -/
theorem bob_line_none_event_eq_point_some
    (kind : LdType) (sample : DirectLdSpace P.extendedDirectLd)
    (readLine : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)) :
    outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun _ answerB => readLine answerB = none) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB =>
          pointGameRead answerA ≠ none ∧ readLine answerB = none) := by
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hpoint : pointGameRead answerA = none
  · simp_all [pointGameRead_eq_none_iff_invalid, outcomeWeight_eq_zero_of_invalid, Or.inl]
  simp_all

/-- Alice's marginal mass of failed completed axis-line evaluation under the
uniform common direct sample. -/
noncomputable def axisAliceNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    aliceEventWeight (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (fun answer => axisGameRead sample answer = none)

/-- Alice's marginal mass of failed completed diagonal-line evaluation under
the uniform common direct sample. -/
noncomputable def diagonalAliceNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    aliceEventWeight (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (fun answer => diagonalGameRead sample answer = none)

/-- Bob's marginal mass of failed completed axis-line evaluation under the
uniform common direct sample. -/
noncomputable def axisBobNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    bobEventWeight (strategy lines)
      (.aline, directLdMap P.extendedDirectLd .aline sample)
      (fun answer => axisGameRead sample answer = none)

/-- Bob's marginal mass of failed completed diagonal-line evaluation under
the uniform common direct sample. -/
noncomputable def diagonalBobNoneMass
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
    bobEventWeight (strategy lines)
      (.dline, directLdMap P.extendedDirectLd .dline sample)
      (fun answer => diagonalGameRead sample answer = none)

/-- At a fixed sample, Alice's failed completed axis evaluation is contained
in the axis-line/point rejection event after zero-mass invalid tags are removed. -/
theorem axis_alice_none_mass_at_le_rejectedMass
    (sample : DirectLdSpace P.extendedDirectLd) :
    aliceEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answer => axisGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) := by
  refine ((outcome_event_weight_left_eq _ _ _ _).symm.trans
    (alice_line_none_event_eq_point_some lines .aline sample _)).trans_le
    ((outcome_event_weight_mono _ _ _ _ _ fun _ _ h => ?_).trans_eq (rejectedMass_eq_read_mismatch lines sample).symm)
  grind

/-- At a fixed sample, Alice's failed completed diagonal evaluation is
contained in the diagonal-line/point rejection event after zero-mass invalid tags are removed. -/
theorem diagonal_alice_none_mass_at_le_rejectedMass
    (sample : DirectLdSpace P.extendedDirectLd) :
    aliceEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answer => diagonalGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) := by
  refine ((outcome_event_weight_left_eq _ _ _ _).symm.trans
    (alice_line_none_event_eq_point_some lines .dline sample _)).trans_le
    ((outcome_event_weight_mono _ _ _ _ _ fun _ _ h => ?_).trans_eq (diagonal_rejectedMass_eq_read_mismatch lines sample).symm)
  grind

/-- At a fixed sample, Bob's failed completed axis evaluation is contained in
the point/axis-line rejection event after zero-mass invalid tags are removed. -/
theorem axis_bob_none_mass_at_le_rejectedMass
    (sample : DirectLdSpace P.extendedDirectLd) :
    bobEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answer => axisGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) := by
  refine ((outcome_event_weight_right_eq _ _ _ _).symm.trans
    (bob_line_none_event_eq_point_some lines .aline sample _)).trans_le
    ((outcome_event_weight_mono _ _ _ _ _ fun _ _ h => ?_).trans_eq (point_axis_rejectedMass_eq_read_mismatch lines sample).symm)
  grind

/-- At a fixed sample, Bob's failed completed diagonal evaluation is
contained in the point/diagonal-line rejection event after zero-mass invalid tags are removed. -/
theorem diagonal_bob_none_mass_at_le_rejectedMass
    (sample : DirectLdSpace P.extendedDirectLd) :
    bobEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answer => diagonalGameRead sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) := by
  refine ((outcome_event_weight_right_eq _ _ _ _).symm.trans
    (bob_line_none_event_eq_point_some lines .dline sample _)).trans_le
    ((outcome_event_weight_mono _ _ _ _ _ fun _ _ h => ?_).trans_eq (point_diagonal_rejectedMass_eq_read_mismatch lines sample).symm)
  grind

/-- Alice's failed completed axis-evaluation mass is bounded by the
axis-line/point branch rejection probability. -/
theorem axis_alice_none_mass_le_rejection
    :
    axisAliceNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .point) := by
  simp [axisAliceNoneMass, directLdBranchRejectionProbability_eq_avgOver, avgOver_mono, axis_alice_none_mass_at_le_rejectedMass]

/-- Alice's failed completed diagonal-evaluation mass is bounded by the
diagonal-line/point branch rejection probability. -/
theorem diagonal_alice_none_mass_le_rejection
    :
    diagonalAliceNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .point) := by
  simp [diagonalAliceNoneMass, directLdBranchRejectionProbability_eq_avgOver, avgOver_mono, diagonal_alice_none_mass_at_le_rejectedMass]

/-- Bob's failed completed axis-evaluation mass is bounded by the
point/axis-line branch rejection probability. -/
theorem axis_bob_none_mass_le_rejection
    :
    axisBobNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .aline) := by
  simp [axisBobNoneMass, directLdBranchRejectionProbability_eq_avgOver, avgOver_mono, axis_bob_none_mass_at_le_rejectedMass]

/-- Bob's failed completed diagonal-evaluation mass is bounded by the
point/diagonal-line branch rejection probability. -/
theorem diagonal_bob_none_mass_le_rejection
    :
    diagonalBobNoneMass lines ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .dline) := by
  simp [diagonalBobNoneMass, directLdBranchRejectionProbability_eq_avgOver, avgOver_mono, diagonal_bob_none_mass_at_le_rejectedMass]

end ExtendedLineGame

end

end MIPStarRE.QPBT
