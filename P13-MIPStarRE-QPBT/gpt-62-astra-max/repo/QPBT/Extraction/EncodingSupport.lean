module

public import QPBT.Algebra.Decoding
public import QPBT.Observables.ExpandedDefs
public import QPBT.Observables.WinImplications.Setup

/-! # Encoding-supported Pauli reference measurements

The reference measurement measures the strategy's Pauli answer and an independent
ideal Pauli answer, then returns the bounded encoding of their sum. Its effects
vanish outside the encoding image. Evaluation of its polynomial outcome is the
convolution of the evaluated strategy measurement and the ideal point projectors.

These are internal auxiliary constructions for blueprint `eq:qld-nonencoding-mass`
and `lem:qld-nonencoding-mass-bound`, not the quantitative support estimate. No
winning premise or global polynomial-pair witness is used or constructed here.

## References

The encoding is paper `eq:low-degree-encoding-definition` in
`references/qpbt-paper/04_preliminaries.tex:882-897`. The convolution is the Pauli
answer replacement of the expanded point measurement at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:383-418`.
The corrected use in `lem:qld-construct-the-paulis` is recorded in blueprint
`eq:qld-nonencoding-mass` and `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

variable {params : AdmissibleParams} {error : ℝ}

/-- The ideal Pauli basis measurement on the ancillary register, bundled using
positivity and completeness of the existing Pauli projectors. -/
noncomputable def pauliRegisterMeas (basis : PauliKind) :
    Measurement (PauliRegister params) (PauliRegister params) :=
  Measurement.ofSumEqOne (pauliProj basis)
    (fun answer => Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj basis answer))
    (sum_pauliProj_eq_one basis)

namespace ProjectiveSetting

variable (setting : ProjectiveSetting params error) (side : PlayerSide) (basis : PauliKind)

/-- Measure the strategy Pauli answer and the ancillary ideal Pauli answer and
return the encoding of their sum. This complete POVM is the internal reference
measurement underlying blueprint `eq:qld-nonencoding-mass`; it is not the global
polynomial measurement whose existence is required in `lem:qld-4-7`. -/
noncomputable def encodingPauliMeas :
    Measurement (Poly params) (setting.ExpandedLocalSpace side) :=
  (tensorMeasurement (setting.pauliMeas side basis) (pauliRegisterMeas basis)).postprocess
    fun answers => encodingPoly (answers.1 + answers.2)

/-- A nonencoding polynomial has zero reference effect. This is exact support of
the auxiliary measurement, not a bound on the global polynomial measurement. -/
theorem encodingPauliMeas_effect_eq_zero_of_not_isEncoding
    (poly : Poly params) (hpoly : ¬ IsEncoding poly) :
    (setting.encodingPauliMeas side basis).effect poly = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro answers hanswers
  exact False.elim (hpoly ((Finset.mem_filter.mp hanswers).2 ▸
    (by
      unfold IsEncoding
      rw [decodeFq_lowDegreeEncoding]
      rfl)))

/-- Evaluating the reference polynomial is equivalent to evaluating the two Pauli
answers separately and adding their values. This uses linearity of the encoding,
not the decoder/evaluation identity for arbitrary polynomial representatives. -/
theorem encodingPauliMeas_postprocess_eval (point : PauliPoint params) :
    (setting.encodingPauliMeas side basis).postprocess (fun poly => evalPoly poly point) =
      (tensorMeasurement (setting.pauliEvalMeas side basis point)
        ((pauliRegisterMeas basis).postprocess
          (fun answer => lowDegreeEnc answer point))).postprocess
        (fun values => values.1 + values.2) := by
  unfold encodingPauliMeas pauliEvalMeas
  simp [Measurement.postprocess_comp, tensorMeasurement_postprocess]
  apply congrArg
  funext answers
  change lowDegreeEnc _ point =
    lowDegreeEnc answers.1 point + lowDegreeEnc answers.2 point
  simp [lowDegreeEnc_eq_dotProduct]

/-- The evaluated reference effects are exactly the Pauli-answer convolution
`K^u_a` in the proof of blueprint `eq:qld-nonencoding-mass`. This identity makes no
approximation or assertion of consistency with the strategy's point measurement. -/
theorem encodingPauliMeas_eval_effect_eq_convolution
    (point : PauliPoint params) (value : PauliScalar params) :
    ((setting.encodingPauliMeas side basis).postprocess
      (fun poly => evalPoly poly point)).effect value =
      ∑ values ∈ Finset.univ.filter
          (fun values : PauliScalar params × PauliScalar params => values.1 + values.2 = value),
        heteroKron ((setting.pauliEvalMeas side basis point).effect values.1)
          (tauPointProj basis point values.2) := by
  simp [encodingPauliMeas_postprocess_eval]
  apply Finset.sum_congr rfl
  intro values _
  simp [lowDegreeEnc_eq_dotProduct]
  rfl

end ProjectiveSetting

end MIPStarRE.QPBT
