module

public import QPBT.Combining.ExtendedLineGame.StateTransport
public import QPBT.Combining.Lines.ConsistencyPositivity

/-!
# Nonnegativity of combining-witness errors

This module derives nonnegativity of the error parameters supplied with the
combined point and extended line witnesses.  The point conclusion follows from
nonnegativity of state-dependent squared distance.  The line conclusion uses
the genuine bipartite POVMs underlying the completed line-point defect.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- Blueprint `lem:qld-4-10` and `lem:qld-4-13`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#335.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- This formalization-only auxiliary records that the error parameter of a supplied
`CombinedPointsWitness` is nonnegative. It supports `lem:qld-4-10`, paper lines
689--709, and does not construct or assert existence of the witness. -/
theorem CombinedPointsWitness.delta_nonneg {P : AdmissibleParams} {epsilon deltaQ : ℝ}
    {setting : ProjectiveSetting P epsilon}
    (points : CombinedPointsWitness setting deltaQ) :
    0 ≤ deltaQ :=
  (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _).trans (points.self_consistent .AA' .BA'' trivial)

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- This formalization-only auxiliary records nonnegativity of the completed
`AA'`--`BA''` line-point defect for a supplied `ExtendedLinesWitness`. It supports
`lem:qld-4-13`, paper lines 1020--1034, by expressing the correlation terms as
those of genuine POVMs on `pairState setting`; it does not construct the witness. -/
theorem completedLinePointDefect_aaBa_nonneg
    (lines : ExtendedLinesWitness setting points deltaL)
    (mu : Distribution
      (DirectLinePointSample P.extendedDirectLd)) :
    0 ≤ completedLinePointDefect lines .AA' .BA'' mu :=
  setting.placedDefect_nonneg .AA' .BA'' mu _ _ trivial

end ExtendedLineGame

/-- This formalization-only auxiliary records that the error parameter of a supplied
`ExtendedLinesWitness` is nonnegative. It supports `lem:qld-4-13`, paper lines
1020--1034, and does not construct or assert existence of the witness. -/
theorem ExtendedLinesWitness.delta_nonneg {P : AdmissibleParams}
    {epsilon deltaQ deltaL : ℝ} {setting : ProjectiveSetting P epsilon}
    {points : CombinedPointsWitness setting deltaQ}
    (lines : ExtendedLinesWitness setting points deltaL) :
    0 ≤ deltaL := by
  exact le_trans
    (ExtendedLineGame.completedLinePointDefect_aaBa_nonneg lines
      (directLinePointDist P.extendedDirectLd))
    (lines.consistent .alice)

end

end MIPStarRE.QPBT
