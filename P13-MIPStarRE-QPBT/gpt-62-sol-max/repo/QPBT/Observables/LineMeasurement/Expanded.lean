module

public import QPBT.Observables.LineMeasurement.Projector

/-!
# Expanded line measurements

This module constructs the expanded line measurements by convolving a strategy
line measurement with the Pauli-register line projectors, and records that the
result is a projective measurement whose effects vanish, on an axis-parallel
line, outside the embedded degree-`d` outcome space. It also introduces the
fine strategy--Pauli product measurement of which the expanded line
measurement is the addition postprocessing, and the evaluation-class and
point-effect families used by the consistency estimates.

## References

The declarations formalize `def:expanded-line-measurement`, whose paper
source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
include S side W line

/-- The line measurement of a projective strategy is again projective: folding
the answers of a line question into a coefficient list is a postprocessing, and
postprocessing preserves projectivity. This is the line analogue of the point
measurement projectivity; both follow because postprocessing preserves
projectivity. The line form is what the projectivity assertion of
`def:expanded-line-measurement` needs, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeas_isProjective :
    MIPStarRE.QPBT.Measurement.IsProjective (S.lineMeas side W line) := by
  apply SandwichProduct.postprocess_isProjective
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- On an axis-parallel line, strategy line effects vanish outside the
embedded degree-`d` subspace: every prescribed answer is a degree-`d`
coefficient list padded by zero. This is the strategy half of the last
assertion of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeas_effect_eq_zero_of_axis
    (haxis : line.kind = .axis) (f : PauliLinePoly P)
    (hf : ¬ f.FitsDegree P.d) :
    (S.lineMeas side W line).effect f = 0 := by
  cases line with
  | diagonal base seed direction baseFixed prefixZero =>
      simp [LineDesc.kind] at haxis
  | axis base seed baseFixed =>
      unfold lineMeas
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      apply Finset.sum_eq_zero
      intro a ha
      exfalso
      apply hf
      rw [← (Finset.mem_filter.mp ha).2]
      intro i hi
      have hi' : ¬ i.val < P.d + 1 := by omega
      cases a <;> simp [lineAnswerOrZero, DegPoly.padTo, padCoefficients, hi']

/-- The convolution of a strategy line effect with the corresponding
Pauli-register line projector. This is the displayed definition of
`hat M^(Line,W),line_f`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def expLineOp
    (f : PauliLinePoly P) : Op (S.ExpandedLocalSpace side) :=
  ∑ pair ∈ Finset.univ.filter
      (fun pair : PauliLinePoly P ×
          PauliLinePoly P => pair.1 + pair.2 = f),
    heteroKron ((S.lineMeas side W line).effect pair.1)
      (tauLineProj P W line pair.2)

/-- The concrete expanded line measurement exhibited in the proof of
`lem:qld-comm-line-cons`. Paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def lineMeasExp :
    Measurement (PauliLinePoly P)
      (S.ExpandedLocalSpace side) :=
  (tensorMeasurement (S.lineMeas side W line) (tauLineMeas P W line)).postprocess
    (fun p => p.1 + p.2)

end

/-- The effects of the expanded line measurement are the convolution
operators. -/
@[simp] theorem lineMeasExp_effect (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : PauliLinePoly P) :
    (S.lineMeasExp side W line).effect f = S.expLineOp side W line f := rfl

/-- The expanded line measurement is projective. This is the projectivity
assertion in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeasExp_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.lineMeasExp side W line) := by
  exact SandwichProduct.postprocess_isProjective _
    (tensorMeasurement_isProjective (S.lineMeas_isProjective side W line)
      (tauLineMeas_isProjective P W line)) _

section

variable (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind)
include S side W

/-- On an axis line, expanded effects outside the embedded degree-`d` outcome
space vanish. This is the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem expLineOp_zero_of_not_deg_d (line : LineDesc P.toLdParams)
    (haxis : line.kind = .axis) (f : PauliLinePoly P)
    (hf : ¬ f.FitsDegree P.d) :
    S.expLineOp side W line f = 0 := by
  unfold expLineOp
  apply Finset.sum_eq_zero
  intro pair hpair
  have hsum := (Finset.mem_filter.mp hpair).2
  by_cases h1 : pair.1.FitsDegree P.d
  · have h2 : ¬ pair.2.FitsDegree P.d := by
      intro h2
      apply hf
      intro i hi
      rw [← hsum, Pi.add_apply, h1 i hi, h2 i hi, add_zero]
    rw [tauLineProj_eq_zero_of_axis P W line haxis pair.2 h2,
      heteroKron_zero_right]
  · rw [S.lineMeas_effect_eq_zero_of_axis side W line haxis pair.1 h1,
      heteroKron_zero_left]

/-- Evaluation classes of the expanded line measurement, including the
explicit `none` class for a non-evaluating canonical line. This is the
completed bracket family used in item 3 of `lem:qld-comm-line-cons`, blueprint
`eq:qld-comm-line-pt-cons2`. -/
noncomputable def lineEvalMeasExp (line : LineDesc P.toLdParams)
    (u : PauliPoint P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.lineMeasExp side W line).postprocess (evalOpt line u)

/-- Complete an expanded point measurement with a zero `none` outcome. This
is the right-hand family in the corrected item 3 of
`lem:qld-comm-line-cons`, blueprint
`eq:qld-comm-line-pt-cons2`. -/
noncomputable def pointMeasExpOption (u : PauliPoint P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.pointMeasExp side W u).postprocess some

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
