module

public import QPBT.Observables.WinImplications.LowDegree

/-!
# Commuting winning implications

This module proves the exact Pair/W and point-trace consistency bounds on
commuting Pauli tuples.

## References

The commuting-tuple consistency theorems prove items 4 and 5
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)
  (z : PauliSpace P) (hcomm : IsCommuting (pauliSharedSplit P z).1)

/-- Select one component of a Pair answer. -/
def selectedPairBit (bits : ZMod 2 × ZMod 2) : ZMod 2 :=
  match W with
  | .X => bits.1
  | .Z => bits.2

/-- Winning the commuting Pair/W branch forces equality of the selected bits. -/
theorem pairLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.pairW W), pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) A B = true) :
    ProjectiveSetting.pairWAnswerOrZero A =
      selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i bit bits
  have hgamma : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := by
    exact hcomm
  cases W <;>
    simp only [pauliPairCondition, hgamma, ne_eq, not_true_eq_false,
      false_or, selectedPairBit] at hwin ⊢ <;>
    exact hwin.symm

/-- The commuting consistency defect is the mismatch probability of source answers. -/
private theorem commConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (S.pairComponentMeas .bob W)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B))) := by
  rw [← consistencyDefect_postprocess_eq_mismatch]
  refine congrArg₂ (fun A B => bipartiteDefect _ A B S.toStrategy.ψ) ?_ ?_ <;> funext x <;>
    first | rfl | simp only [ProjectiveSetting.pairComponentMeas, ProjectiveSetting.pairMeas, MIPStarRE.Quantum.Measurement.postprocess_comp] <;> rfl

end

/-- On commuting tuples, Pair/W answers agree with the corresponding
component of Pair answers. This is item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`lem:qld-win-implications`. -/
theorem win_comm_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (commTupleDist P)
        (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (S.pairComponentMeas .bob W)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  rw [commConsistency_eq_mismatch]
  calc
    _ ≤ _ := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      apply outcome_event_weight_nonneg
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pairWPairEdge W)) := by
      gcongr
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp_all
        have hs : outcomeEventWeight S.toStrategy ((.pairW W), pauliCL _ (.pairW W) z) (.pair, pauliCL _ .pair z) (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠ selectedPairBit W (ProjectiveSetting.pairAnswerOrZero B)) ≤ pauliRejectionAt S.toStrategy (pairWPairEdge W) z := by
               apply outcome_event_weight_mono
               intro A B hne
               apply Bool.eq_false_iff.mpr
               intro htrue
               exact hne (pairLabels_eq_of_win _ W z A B hcomm htrue)
        exact hs
      · simp_all
        apply pauliRejectionAt_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)

section

variable (W : PauliKind) {P : AdmissibleParams} (ω : PauliTuple P)

/-- Select the point coordinate of a shared Pauli tuple in one basis. -/
def selectedTuplePoint : PauliPoint P :=
  match W with
  | .X => ω.1
  | .Z => ω.2.1

/-- Select the scalar multiplier of a shared Pauli tuple in one basis. -/
def selectedTupleScalar : PauliScalar P :=
  match W with
  | .X => ω.2.2.1
  | .Z => ω.2.2.2

end

section

variable (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) (ω : PauliTuple P)
  (A B : PauliAnswer P)

/-- The binary trace label extracted from a point answer. -/
def pointTraceLabel : ZMod 2 :=
  fixedBinTrace P.model
    (ProjectiveSetting.pointAnswerOrZero A * selectedTupleScalar W ω)

/-- Winning the commuting point/Pair-W branch forces equality of trace labels. -/
theorem pointPairLabels_eq_of_win
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.pairW W), pauliCL P (.pairW W) z) A B = true) :
    fixedBinTrace P.model
        (ProjectiveSetting.pointAnswerOrZero A *
          selectedTupleScalar W (pauliSharedSplit P z).1) =
      ProjectiveSetting.pairWAnswerOrZero B := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a bit
  simp [ProjectiveSetting.pointAnswerOrZero, ProjectiveSetting.pairWAnswerOrZero]
  have hgamma : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := by
    exact hcomm
  rw [pauliCL_shared_eq P (.pairW W) rfl] at hwin
  cases W with
  | X =>
      rcases hwin with hne | heq
      · exact (hne hgamma).elim
      · exact heq
  | Z =>
      rcases hwin with hne | heq
      · exact (hne hgamma).elim
      · exact heq

end

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

/-- Point-trace/Pair-W consistency is the mismatch probability of source answers. -/
theorem commConsConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
        (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (ProjectiveSetting.pairWQuestion P W
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  rw [← consistencyDefect_postprocess_eq_mismatch]
  refine congrArg₂ (fun A B => bipartiteDefect _ A B S.toStrategy.ψ) ?_ ?_ <;> funext x <;>
    first | rfl | simp only [ProjectiveSetting.pointTraceMeas, ProjectiveSetting.pointMeas, MIPStarRE.Quantum.Measurement.postprocess_comp] <;> rfl

end

/-- On commuting tuples, trace-coarse-grained point answers agree with Pair/W
answers. This is item 5 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-239`, blueprint
`lem:qld-win-implications`. -/
theorem win_comm_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (commTupleDist P)
        (fun ω => S.pointTraceMeas .alice W
        (match W with | .X => ω.1 | .Z => ω.2.1)
        (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2))
        (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  change bipartiteDefect (commTupleDist P)
      (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
      _
      S.toStrategy.ψ ≤ _
  rw [commConsConsistency_eq_mismatch]
  calc
    _ ≤ _ := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      apply outcome_event_weight_nonneg
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pointPairWEdge W)) := by
      gcongr
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp_all
        have hs : outcomeEventWeight S.toStrategy ((.point W), pauliCL _ (.point W) z) ((.pairW W), pauliCL _ (.pairW W) z) (fun A B => pointTraceLabel _ W (pauliSharedSplit _ z).1 A ≠ ProjectiveSetting.pairWAnswerOrZero B) ≤ pauliRejectionAt S.toStrategy (pointPairWEdge W) z := by
               apply outcome_event_weight_mono
               intro A B hne
               apply Bool.eq_false_iff.mpr
               intro htrue
               exact hne (pointPairLabels_eq_of_win _ W z A B hcomm htrue)
        exact hs
      · simp_all
        apply pauliRejectionAt_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)

end WinImplications

end

end MIPStarRE.QPBT
