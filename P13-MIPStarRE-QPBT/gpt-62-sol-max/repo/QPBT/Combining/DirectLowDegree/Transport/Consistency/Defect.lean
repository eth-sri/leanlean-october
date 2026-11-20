module

public import QPBT.Combining.DirectLowDegree.Transport.Consistency.State

/-!
# Low-degree consistency defect transport

This module expresses the consistency conclusions of the low individual
degree theorem in the coordinates of the directly indexed game, without
changing their numerical bounds.  The point/polynomial and polynomial/point
conclusions are taken at a fixed tuple coordinate; the polynomial/polynomial
conclusion is global.

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

noncomputable section

/-- The direct game's point readout, with ill-formed answers folded into zero. -/
noncomputable abbrev directLdPointReadout {D : DirectLdParams} {I : Type*}
    [Fintype I] [DecidableEq I]
    (M : DirectLdQuestion D → Quantum.Measurement (DirectLdAnswer D) I)
    (u : DirectPoint D) :=
  (M (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D)

/-- The two point-versus-polynomial bounds and the polynomial agreement bound. -/
abbrev DirectLdConsistency {D : DirectLdParams} (S : Strategy (directLdGame D))
    (GA : DirectPolyMeasTuple D S.ιA) (GB : DirectPolyMeasTuple D S.ιB)
    (pointError polynomialError : ℝ) : Prop :=
  bipartiteDefect (uniformDistribution (DirectPoint D))
      (directLdPointReadout S.A) (fun u => GB.postprocess (evalDirectPolyTupleAt u)) S.ψ ≤
      pointError ∧
  bipartiteDefect (uniformDistribution (DirectPoint D))
      (fun u => GA.postprocess (evalDirectPolyTupleAt u)) (directLdPointReadout S.B) S.ψ ≤
      pointError ∧
  bipartiteDefect (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ ≤ polynomialError

/-! ## The three LDT conclusions in direct coordinates -/

/-- A complete LDT consistency relation gives the corresponding vector
bound after relabeling questions and outcomes by equivalences. -/
private theorem reindexedConsRel_defect_le {G : Game} (S : Strategy G)
    {X Y a b : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : X ≃ Y) (o : a ≃ b)
    (A : X → MIPStarRE.Quantum.Measurement a S.ιA)
    (B : X → MIPStarRE.Quantum.Measurement a S.ιB)
    (A' : Y → ProjMeas b S.ιA) (B' : Y → ProjMeas b S.ιB)
    (ha : ∀ x v, (A x).effect v = (A' (e x)).outcome (o v))
    (hb : ∀ x v, (B x).effect v = (B' (e x)).outcome (o v)) {δ : ℝ}
    (h : ConsRel (strategyQuantumState S) (uniformDistribution Y)
      (fun y => (A' y).toSubMeas) (fun y => (B' y).toSubMeas) δ) :
    bipartiteDefect (uniformDistribution X) A
      B S.ψ ≤ δ := by
  have ht := strategyConsRel_consistencyDefect_le S _ (uniformDistribution_isProbability Y) A' B' δ h
  rw [← consistencyDefect_uniform_question_outcome_equiv e o] at ht
  grind only

section

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
include D S

/-- Convert the point-on-Alice/global-on-Bob conclusion of `LDT.Test.mainFormal`
for one simultaneous coordinate to the direct QPBT defect, with the identical
numerical bound. -/
theorem directPointPolynomial_consistencyDefect_le
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementA)
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta →
        bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPointCoordinateMeasurementA D S r)
          (directPolynomialEvaluationMeasurement D G)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  exact reindexedConsRel_defect_le S (directPointEquiv D) (directScalarEquiv D)
    (directPointCoordinateMeasurementA D S r) (directPolynomialEvaluationMeasurement D G)
    ((directCoordinateProjStrat D S hS r).pointMeasurementA) (ldtPolynomialEvaluationMeasurement D G)
    (directCoordinatePointMeasurement_effect_transport D S.A hS.1 r)
    (directPolynomialMeasurement_evaluation_effect D G) h

/-- Convert the global-on-Alice/point-on-Bob conclusion of
`LDT.Test.mainFormal` for one simultaneous coordinate to the direct QPBT
defect, with the identical numerical bound. -/
theorem directPolynomialPoint_consistencyDefect_le
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat D S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat D S hS r).pointMeasurementB) delta →
        bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPolynomialEvaluationMeasurement D G)
          (directPointCoordinateMeasurementB D S r)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  exact reindexedConsRel_defect_le S (directPointEquiv D) (directScalarEquiv D)
    (directPolynomialEvaluationMeasurement D G) (directPointCoordinateMeasurementB D S r)
    (ldtPolynomialEvaluationMeasurement D G) ((directCoordinateProjStrat D S hS r).pointMeasurementB)
    (directPolynomialMeasurement_evaluation_effect D G)
    (directCoordinatePointMeasurement_effect_transport D S.B hS.2 r) h

/-- Convert the global/global conclusion of `LDT.Test.mainFormal` to the direct
QPBT defect, with the identical numerical bound. -/
theorem directPolynomialPolynomial_consistencyDefect_le :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (strategyQuantumState S) (uniformDistribution Unit)
          (constSubMeasFamily GA.toSubMeas)
          (constSubMeasFamily GB.toSubMeas) delta →
        bipartiteDefect (uniformDistribution Unit)
          (fun _ => directPolynomialMeasurement D GA)
          (fun _ => directPolynomialMeasurement D GB)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro GA GB delta h
  exact reindexedConsRel_defect_le S (Equiv.refl Unit) (directPolyEquivPolynomial D)
    (fun _ => directPolynomialMeasurement D GA) (fun _ => directPolynomialMeasurement D GB)
    (fun _ => GA) (fun _ => GB) (fun _ => directPolynomialMeasurement_effect D GA)
    (fun _ => directPolynomialMeasurement_effect D GB) h

end

end

end MIPStarRE.QPBT
