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

/-- Winning the commuting Pair/W branch forces equality of the selected bits. -/
theorem pairLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.pairW W), pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) A B = true) :
    ProjectiveSetting.pairWAnswerOrZero A =
      W.component (ProjectiveSetting.pairAnswerOrZero B) := by
  have hg : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := hcomm
  cases A <;> cases B <;> simp [pauliWinPredicate, validPauliAnswer] at hwin
  cases W <;> simp_all [pauliPairCondition, PauliKind.component, ProjectiveSetting.pairWAnswerOrZero, ProjectiveSetting.pairAnswerOrZero, eq_comm]

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

/-- Commuting Pair/W mismatch is contained in rejection. -/
private theorem pairMismatch_le_rejection (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.pairW W), pauliCL P (.pairW W) z)
        (.pair, pauliCL P .pair z)
        (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
          W.component (ProjectiveSetting.pairAnswerOrZero B)) ≤
      pauliRejectionAt S.toStrategy
        (pairWPairEdge W) z :=
  mismatch_le_pauliRejectionAt S.toStrategy (pairWPairEdge W) z _ _
    (fun A B => pairLabels_eq_of_win P W z A B hcomm)

/-- The commuting consistency defect is the mismatch probability of source answers. -/
private theorem commConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (S.pairWAt .alice W)
        (S.pairComponentMeas .bob W)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            W.component (ProjectiveSetting.pairAnswerOrZero B))) := by
  let qA : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : PauliTuple P → PauliQuestion P := fun ω =>
    ProjectiveSetting.pairQuestion P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ =>
    ProjectiveSetting.pairWAnswerOrZero
  let fB : PauliTuple P → PauliAnswer P → ZMod 2 := fun _ B =>
    W.component (ProjectiveSetting.pairAnswerOrZero B)
  refine (consistencyDefect_congr _ _ _ _ _ _ ?_ ?_).trans
    (consistencyDefect_postprocess_eq_mismatch
        (commTupleDist P) S.toStrategy qA qB fA fB)
  · intro ω c
    rfl
  · intro ω c
    congr 1
    unfold ProjectiveSetting.pairComponentMeas ProjectiveSetting.pairAt ProjectiveSetting.pairMeas fB qB
    rw [Measurement.postprocess_comp]
    rfl

end

/-- On commuting tuples, Pair/W answers agree with the corresponding
component of Pair answers. This is item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`lem:qld-win-implications`. -/
theorem win_comm_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (commTupleDist P)
        (S.pairWAt .alice W)
        (S.pairComponentMeas .bob W)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  rw [commConsistency_eq_mismatch]
  refine (avgOver_comm_le_two_mul_gated P _ (fun _ => outcome_event_weight_nonneg _ _ _ _)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (avgOver_gated_le_fixedEdge S (pairWPairEdge W) _ _ ?_) (by norm_num)
  intro z hz
  have h := pairMismatch_le_rejection S W z hz
  rw [pauliCL_shared_eq P (.pairW W) rfl, pauliCL_shared_eq P .pair rfl] at h
  exact h

section

variable (P : AdmissibleParams) (W : PauliKind)
include P W

/-- The binary trace label extracted from a point answer. -/
def pointTraceLabel
    (ω : PauliTuple P) (A : PauliAnswer P) : ZMod 2 :=
  fixedBinTrace P.model
    (ProjectiveSetting.pointAnswerOrZero A * ω.scalar W)

/-- The point coordinate of the low-degree projection is the selected shared block. -/
theorem pauliToLd_point_eq_selected
    (z : PauliSpace P) :
    (pauliToLd P W z).point = (pauliSharedSplit P z).1.point W := by
  funext i
  cases W <;> rfl

/-- Winning the commuting point/Pair-W branch forces equality of trace labels. -/
theorem pointPairLabels_eq_of_win
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.pairW W), pauliCL P (.pairW W) z) A B = true) :
    fixedBinTrace P.model
        (ProjectiveSetting.pointAnswerOrZero A *
          (pauliSharedSplit P z).1.scalar W) =
      ProjectiveSetting.pairWAnswerOrZero B := by
  have hg : pauliPairGamma P (pauliCL P (.pairW W) z) = 0 := hcomm
  cases A <;> cases B <;> simp [pauliWinPredicate, validPauliAnswer] at hwin
  have hr : pauliTraceFactor W (pauliCL P (.pairW W) z) =
      (pauliSharedSplit P z).1.scalar W := by cases W <;> rfl
  simp_all [pauliPointPairCondition, ProjectiveSetting.pointAnswerOrZero, ProjectiveSetting.pairWAnswerOrZero]

end

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

/-- Commuting point-trace/Pair-W mismatch is contained in rejection. -/
theorem pointPairMismatch_le_rejection (z : PauliSpace P)
    (hcomm : IsCommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.pairW W), pauliCL P (.pairW W) z)
        (fun A B =>
          pointTraceLabel P W (pauliSharedSplit P z).1 A ≠
            ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy
        (pointPairWEdge W) z :=
  mismatch_le_pauliRejectionAt S.toStrategy (pointPairWEdge W) z _ _ (fun A B => pointPairLabels_eq_of_win P W z A B hcomm)

/-- For a trace-point measurement, the mismatch event reads the trace of the raw answer. -/
theorem pointTraceAt_defect_eq (μ : Distribution (PauliTuple P))
    (q : PauliTuple P → PauliQuestion P) (g : PauliAnswer P → ZMod 2)
    {R : PauliTuple P → Measurement (ZMod 2) S.toStrategy.ιB}
    (hR : ∀ ω, R ω = (S.toStrategy.B (q ω)).postprocess g) :
    bipartiteDefect μ (S.pointTraceAt .alice W) R S.toStrategy.ψ =
      avgOver μ (fun ω => outcomeEventWeight S.toStrategy
        (ProjectiveSetting.pointQuestion P W (ω.point W)) (q ω)
        (fun a b => pointTraceLabel P W ω a ≠ g b)) := by
  rw [funext hR]
  refine (consistencyDefect_congr _ _ _ _ _ _ ?_ (fun _ _ => rfl)).trans
    (consistencyDefect_postprocess_eq_mismatch μ S.toStrategy _ q
      (pointTraceLabel P W) (fun _ => g))
  intro ω a
  simp only [ProjectiveSetting.pointTraceAt, ProjectiveSetting.pointTraceMeas,
    ProjectiveSetting.pointMeas, Measurement.postprocess_comp]
  rfl

/-- Point-trace/Pair-W consistency is the mismatch probability of source answers. -/
theorem commConsConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (S.pointTraceAt .alice W)
        (S.pairWAt .bob W)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (ω.point W))
          (ProjectiveSetting.pairWQuestion P W
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) :=
  pointTraceAt_defect_eq S W _ (fun ω => ProjectiveSetting.pairWQuestion P W
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) _ (fun _ => rfl)

end

/-- On commuting tuples, trace-coarse-grained point answers agree with Pair/W
answers. This is item 5 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-239`, blueprint
`lem:qld-win-implications`. -/
theorem win_comm_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (commTupleDist P)
        (S.pointTraceAt .alice W)
        (S.pairWAt .bob W)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  rw [commConsConsistency_eq_mismatch]
  refine (avgOver_comm_le_two_mul_gated P _ (fun _ => outcome_event_weight_nonneg _ _ _ _)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (avgOver_gated_le_fixedEdge S (pointPairWEdge W) _ _ ?_) (by norm_num)
  intro z hz
  have h := pointPairMismatch_le_rejection S W z hz
  rw [pauliCL_point_eq, pauliCL_shared_eq P (.pairW W) rfl, pauliToLd_point_eq_selected] at h
  exact h

end WinImplications

end

end MIPStarRE.QPBT
