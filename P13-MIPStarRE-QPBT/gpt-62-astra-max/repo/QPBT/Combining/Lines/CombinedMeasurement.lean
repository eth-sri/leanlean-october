module

public import QPBT.Combining.Witnesses

/-!
# Combined X/Z line measurement

This module constructs the X-Z-X sandwich POVM used to combine one X-line
measurement with one Z-line measurement.  It also records the orientation of
the sandwich as a one-sided pasted measurement and the two axis-degree support
properties.

## References

The construction is the paired-line measurement in `lem:qld-xz-lines`, with
source `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-949`.
Its separate blueprint entries are `def:concrete-paired-line-measurement` and
`lem:concrete-paired-line-degree-support`; consistency remains the distinct
obligation `lem:combined-line-measurement-consistency`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
  (lineX lineZ : LineDesc P.toLdParams)

/-- The paired-line POVM in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-949`. The X effect is the outer
projector. This construction does not assert consistency with a point witness. -/
def ProjectiveSetting.combinedLineMeasurement :
    Quantum.Measurement (PauliLinePoly P ×
      PauliLinePoly P) (S.ExpandedLocalSpace side) :=
  Measurement.congrAlphabet (Equiv.prodComm _ _)
    (pastedPOVM (S.lineMeasExp side .Z lineZ) (S.lineMeasExp_isProjective side .X lineX))

section

variable (fX fZ : PauliLinePoly P)

/-- The effects of the paired-line POVM are the source's X-Z-X sandwiches. -/
@[simp] theorem ProjectiveSetting.combinedLineMeasurement_effect :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX *
        (S.lineMeasExp side .Z lineZ).effect fZ *
        (S.lineMeasExp side .X lineX).effect fX := rfl

/-- The X-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_X
    (haxis : lineX.kind = .axis) (hf : ¬ fX.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp [S.combinedLineMeasurement_effect, S.lineMeasExp_effect, S.expLineOp_zero_of_not_deg_d side .X lineX haxis fX hf]

/-- The Z-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_Z
    (haxis : lineZ.kind = .axis) (hf : ¬ fZ.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp [S.combinedLineMeasurement_effect, S.lineMeasExp_effect, S.expLineOp_zero_of_not_deg_d side .Z lineZ haxis fZ hf]

end

end

end MIPStarRE.QPBT
