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

open DistanceCalculus

local notation "D" => P.extendedDirectLd
local notation "Sample" => DirectLdSpace D
local notation "Read" => Sample → DirectLdAnswer D → Option (PauliScalar P)
local notation "I" => setting.ExpandedLocalSpace PlayerSide.alice ×
  setting.ExpandedLocalSpace PlayerSide.bob

section

variable (lines : ExtendedLinesWitness setting points deltaL)
include lines

/-- The defect of Alice's and Bob's completed readouts for the same line. -/
abbrev sameLineEvaluationDefect
    (kind : LineKind) :=
  readoutDefect lines (lineTag kind) (lineTag kind) (lineGameRead kind) (lineGameRead kind)

/-- The readouts of either line type compare via the same two point readouts. -/
private theorem same_line_evaluation_defect_le (tag : LdType) (read : Read)
    (hLP : readoutDefect lines tag .point read (fun _ => pointGameRead) =
      branchRejection lines tag .point)
    (hPL : readoutDefect lines .point tag (fun _ => pointGameRead) read =
      branchRejection lines .point tag)
    (hL : branchRejection lines tag .point ≤ 2 * deltaL)
    (hR : branchRejection lines .point tag ≤ 2 * deltaL) :
    readoutDefect lines tag tag read read ≤ 2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  let A t (r : Read) : Sample → Measurement (Option (PauliScalar P)) I := fun x =>
    leftPlacedMeasurement (sampleReadout lines .alice t r x)
  let B t (r : Read) : Sample → Measurement (Option (PauliScalar P)) I := fun x =>
    rightPlacedMeasurement (sampleReadout lines .bob t r x)
  let pt : Read := fun _ => pointGameRead
  have h := consistencyDefect_trans_le (uniformDistribution Sample)
    (A tag read) (B .point pt) (A .point pt) (B tag read) (pairState setting) _ _ _
    (uniformDistribution_isProbability _) (pairState_norm setting)
    hLP.le (point_read_defect_on_direct_samples_eq_rejection lines).le hPL.le
  refine h.trans ?_
  have hp := point_point_rejection_le lines
  exact add_le_add hL (by gcongr)

/-- The same-line defect is bounded via the two point readouts. -/
theorem sameLineEvaluationDefect_le (kind : LineKind) :
    sameLineEvaluationDefect lines kind ≤ 2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) :=
  same_line_evaluation_defect_le lines (lineTag kind) (lineGameRead kind)
    (readoutDefect_eq_branchRejection lines _ _ _ _ (line_point_rejectedMass_eq_read_mismatch lines kind))
    (readoutDefect_eq_branchRejection lines _ _ _ _ (point_line_rejectedMass_eq_read_mismatch lines kind))
    (line_point_rejection_le lines kind) (point_line_rejection_le lines kind)

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
