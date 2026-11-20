module

public import QPBT.Combining.ExtendedLineGame.PointPointRejection

/-!
# Completed same-line evaluation comparison

This module compares Alice's and Bob's completed axis-line or diagonal-line
readouts through the corresponding point readouts. The comparison uses the
consistency triangle on the common direct-game sample and then applies the
already proved mixed and point/point branch bounds.

The readouts take values in `Option (PauliScalar P)`. Agreement on `none`, in
particular for zero directions, is not an equality of parameter evaluations;
no coefficient-collision conclusion is asserted here.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#321.
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

variable (lines : ExtendedLinesWitness setting points deltaL)

/-- The question tag and completed readout of either sort of line. -/
def lineTag : LineKind → LdType | .axis => .aline | .diagonal => .dline

def lineRead : LineKind → DirectLdSpace P.extendedDirectLd → Readout P
  | .axis => axisGameRead
  | .diagonal => diagonalGameRead

theorem linePointLaw (k : LineKind) :
    BranchReadLaw (lineTag k) .point (lineRead (P := P) k) (fun _ => pointGameRead) := by
  cases k
  · exact axisPointReadLaw
  · exact diagonalPointReadLaw

abbrev rejection (i j : LdType) :=
  directLdBranchRejectionProbability (strategy lines) (i, j)

/-- Compare two line readouts through the intervening point readouts. -/
private theorem same_line_evaluation_chain (i : LdType) (f : DirectLdSpace P.extendedDirectLd → Readout P)
    (h : BranchReadLaw i .point f (fun _ => pointGameRead)) :
    branchReadDefect lines i i f f ≤ rejection lines i .point +
      2 * Real.sqrt (rejection lines .point .point + rejection lines .point i) := by
  let A j g s := DistanceCalculus.leftPlacedMeasurement (ιB := setting.ExpandedLocalSpace .bob)
    (readMeasurement lines .alice j g s)
  let B j g s := DistanceCalculus.rightPlacedMeasurement (ιA := setting.ExpandedLocalSpace .alice)
    (readMeasurement lines .bob j g s)
  exact consistencyDefect_trans_le _ (A i f) (B .point (fun _ => pointGameRead))
    (A .point (fun _ => pointGameRead)) (B i f) _ _ _ _ (uniformDistribution_isProbability _)
    (pairState_norm setting) (rejection_eq_readDefect lines h).symm.le
    (rejection_eq_readDefect lines pointPointReadLaw).symm.le
    (rejection_eq_readDefect lines h.swap).symm.le

theorem mixed_bounds (k : LineKind) :
    rejection lines (lineTag k) .point ≤ 2 * deltaL ∧
      rejection lines .point (lineTag k) ≤ 2 * deltaL := by
  have ⟨hf, hr⟩ := completedLinePointDefect_sums_le lines
  rw [← aline_point_rejection_eq_completedLinePointDefect,
    ← dline_point_rejection_eq_completedLinePointDefect] at hf
  rw [← point_aline_rejection_eq_completedLinePointDefect,
    ← point_dline_rejection_eq_completedLinePointDefect] at hr
  have hn (i j) : 0 ≤ rejection lines i j := directLdBranchRejectionProbability_nonneg _ _ _
  dsimp only [rejection] at *
  cases k <;> constructor <;> dsimp only [lineTag] <;> linarith [hn .aline .point, hn .point .aline, hn .dline .point, hn .point .dline]

/-- Both kinds of completed line readouts obey the same square-root loss. -/
theorem same_line_evaluation_le (k : LineKind) :
    branchReadDefect lines (lineTag k) (lineTag k) (lineRead k) (lineRead k) ≤
      2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have b := mixed_bounds lines k
  refine (same_line_evaluation_chain lines _ _ (linePointLaw k)).trans (add_le_add b.1 ?_)
  gcongr
  · exact point_point_rejection_le lines
  · exact b.2

end ExtendedLineGame
end
end MIPStarRE.QPBT
