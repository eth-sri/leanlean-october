module

public import MIPStarRE.LDT.Test.StrategyRole.Algebra
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Measurements
public import QPBT.Games.DistanceTheorems.TensorSupport

/-!
# State conversion and direct point readout

This module contains the pure-state conversion and direct point-readout
portion of the low-degree consistency transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

/-- An LDT consistency relation on the density state associated with a game
strategy gives the identical QPBT defect bound on the strategy vector. -/
theorem strategyConsRel_consistencyDefect_le
    {G : Game} (S : Strategy G)
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (mu : Distribution Question) (_hmu : mu.IsProbability)
    (A : Question → ProjMeas Outcome S.ιA)
    (B : Question → ProjMeas Outcome S.ιB) (delta : ℝ)
    (h : ConsRel (strategyQuantumState S) mu
      (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta) :
    consistencyDefect mu
      (fun x a => heteroKron ((A x).outcome a) 1)
      (fun x a => heteroKron 1 ((B x).outcome a)) S.ψ ≤ delta := by
  letI := (strategyQuantumState_isNormalized S).nonempty
  have hv : pureStateEuclideanVector (strategyPureState S) = S.ψ :=
    (EuclideanSpace.equiv _ ℂ).injective rfl
  simpa only [hv] using
    (ldt_consRel_iff_consistencyDefect (strategyPureState S) mu
      (fun x => (A x).toMeasurement) (fun x => (B x).toMeasurement) delta).mp h

@[simp] theorem directPointQuestionOf_directPointEquiv
    (D : DirectLdParams) (u : DirectPoint D) :
    directPointQuestionOf D (directPointEquiv D u) =
      directLdPointQuestionOf D u := by
  unfold directPointQuestionOf ldtPointToDirect
  rw [(directPointEquiv D).symm_apply_apply]

/-- The zero vector witnesses that the space of LDT points associated with
directly indexed parameters is nonempty. -/
instance directLdtPointNonempty (D : DirectLdParams) :
    Nonempty (Point D.toLDTParameters) :=
  ⟨fun _ => ⟨0, D.toLDTParameters.hq⟩⟩

section

variable (D : DirectLdParams)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)

/-- The LDT scalar readout is the direct coordinate readout followed by
the scalar coding equivalence. -/
@[simp] theorem directPointAnswerReadout_eq
    (D : DirectLdParams) (r : Fin D.k) (answer : DirectLdAnswer D) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r answer =
      directScalarEquiv D (directLdPointValuesOrZero D answer r) := by
  letI := D.toLDTFieldModel
  cases answer <;> rfl

/-- Coordinate readout of a direct point measurement. -/
noncomputable def directPointCoordinateMeasurement
    (r : Fin D.k) (u : DirectPoint D) :
    MIPStarRE.Quantum.Measurement (DirectScalarQ D) ι :=
  (M (directLdPointQuestionOf D u)).postprocess (fun a => directLdPointValuesOrZero D a r)

noncomputable abbrev directPointCoordinateMeasurementA
    (D : DirectLdParams) (S : Strategy (directLdGame D)) := directPointCoordinateMeasurement D S.A

noncomputable abbrev directPointCoordinateMeasurementB
    (D : DirectLdParams) (S : Strategy (directLdGame D)) := directPointCoordinateMeasurement D S.B

/-- The LDT and direct coordinate readouts agree over corresponding alphabets. -/
theorem directCoordinatePointMeasurement_effect_transport
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) (r : Fin D.k)
    (u : DirectPoint D) (a : DirectScalarQ D) :
    letI := D.toLDTFieldModel
    (directPointCoordinateMeasurement D M r u).effect a =
      (directCoordinatePointMeasurement D r M hM (directPointEquiv D u)).outcome (directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  classical
  simp only [directPointCoordinateMeasurement, directCoordinatePointMeasurement, directCoordinateReadout,
    ProjMeas.postprocess, SubMeas.postprocess_outcome, matrixMeasurementToLDTProjMeas_outcome,
    directPointQuestionOf_directPointEquiv, MIPStarRE.Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  simp [directPointAnswerReadout_eq]

end

/-- Evaluate a transported LDT polynomial measurement at a direct point. -/
noncomputable def directPolynomialEvaluationMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        (DirectPoint D) →
          MIPStarRE.Quantum.Measurement (DirectScalarQ D) iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u
  exact (directPolynomialMeasurement D G).postprocess
    (fun g => MvPolynomial.eval u g.1)

/-- The LDT projective evaluation family associated with a global
polynomial projective measurement. -/
noncomputable def ldtPolynomialEvaluationMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u
  exact ProjMeas.postprocess G (fun g => g u)

end

end MIPStarRE.QPBT
