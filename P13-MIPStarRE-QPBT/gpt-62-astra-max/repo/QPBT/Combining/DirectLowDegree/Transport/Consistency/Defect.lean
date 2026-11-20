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

/-! ## The three LDT conclusions in direct coordinates -/

variable (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective)
  (r : Fin D.k)

/-- The direct single-coordinate point/global defect is exactly the LDT
defect after the polynomial, point, and scalar equivalences. -/
theorem directPointPolynomial_consistencyDefect_eq :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPointCoordinateMeasurementA D S r)
          (directPolynomialEvaluationMeasurement G) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (ldtPointAPlaced D S hS r)
          (ldtPolynomialEvaluationRight D G) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  rw [← consistencyDefect_uniform_question_outcome_equiv
    (directPointEquiv D) (directScalarEquiv D)
    (ldtPointAPlaced D S hS r)
    (ldtPolynomialEvaluationRight D G) S.ψ]
  apply consistencyDefect_congr
  · intro u a
    unfold ldtPointAPlaced
    congr 1
    exact (directCoordinatePointMeasurement_effect_transport
      D S hS r u a).symm
  · intro u a
    unfold ldtPolynomialEvaluationRight
    congr 1
    apply directPolynomialMeasurement_evaluation_effect

/-- Convert the point-on-Alice/global-on-Bob conclusion of `LDT.Test.mainFormal`
for one simultaneous coordinate to the direct QPBT defect, with the identical
numerical bound. -/
theorem directPointPolynomial_consistencyDefect_le :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat S hS r).pointMeasurementA)
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas) delta →
        bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPointCoordinateMeasurementA D S r)
          (directPolynomialEvaluationMeasurement G)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  rw [directPointPolynomial_consistencyDefect_eq D S hS r G]
  apply strategyConsRel_consistencyDefect_le S
    _
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (ldtCoordinatePointMeasurementA D S hS r)
    (ldtPolynomialEvaluationMeasurement D G) delta
  exact h

/-- The direct single-coordinate global/point defect is exactly the LDT
defect after the polynomial, point, and scalar equivalences. -/
theorem directPolynomialPoint_consistencyDefect_eq :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA),
      bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPolynomialEvaluationMeasurement G)
          (directPointCoordinateMeasurementB D S r) S.ψ =
        consistencyDefect (uniformDistribution (Point D.toLDTParameters))
          (ldtPolynomialEvaluationLeft D G)
          (ldtPointBPlaced D S hS r) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  rw [← consistencyDefect_uniform_question_outcome_equiv
    (directPointEquiv D) (directScalarEquiv D)
    _
    _ S.ψ]
  apply consistencyDefect_congr
  · intro u a
    unfold ldtPolynomialEvaluationLeft
    congr 1
    apply directPolynomialMeasurement_evaluation_effect
  · intro u a
    unfold ldtPointBPlaced
    congr 1
    exact (directCoordinatePointMeasurementB_effect_transport
      D S hS r u a).symm

/-- Convert the global-on-Alice/point-on-Bob conclusion of
`LDT.Test.mainFormal` for one simultaneous coordinate to the direct QPBT
defect, with the identical numerical bound. -/
theorem directPolynomialPoint_consistencyDefect_le :
    letI := D.toLDTFieldModel
    ∀ (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (delta : ℝ),
      ConsRel (directCoordinateProjStrat S hS r).state
          (uniformDistribution (Point D.toLDTParameters))
          (polynomialEvaluationFamily D.toLDTParameters G.toSubMeas)
          (IdxProjMeas.toIdxSubMeas
            (directCoordinateProjStrat S hS r).pointMeasurementB) delta →
        bipartiteDefect
          (uniformDistribution (DirectPoint D))
          (directPolynomialEvaluationMeasurement G)
          (directPointCoordinateMeasurementB D S r)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro G delta h
  have hldt := strategyConsRel_consistencyDefect_le S
    _
    (uniformDistribution_isProbability (Point D.toLDTParameters))
    (ldtPolynomialEvaluationMeasurement D G)
    _ delta (h)
  simp [directPolynomialPoint_consistencyDefect_eq D S hS r G]
  exact hldt

/-- Relabeling both global polynomial measurements identifies their direct
QPBT defect with the LDT global/global defect. -/
theorem directPolynomialPolynomial_consistencyDefect_eq :
    letI := D.toLDTFieldModel
    ∀ (GA : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      bipartiteDefect (uniformDistribution Unit)
          (fun _ => directPolynomialMeasurement GA)
          (fun _ => directPolynomialMeasurement GB)
          S.ψ =
        consistencyDefect (uniformDistribution Unit)
          (fun _ g => ldtPolynomialLeftPlaced D GA g)
          (fun _ g => ldtPolynomialRightPlaced D GB g) S.ψ := by
  letI := D.toLDTFieldModel
  intro GA GB
  rw [← consistencyDefect_outcome_equiv _
    (directPolyEquivPolynomial D)
    _
    _ S.ψ]
  apply consistencyDefect_congr
  · intros; apply heteroKron.eq_1
  · intros; apply heteroKron.eq_1

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
          (fun _ => directPolynomialMeasurement GA)
          (fun _ => directPolynomialMeasurement GB)
          S.ψ ≤ delta := by
  letI := D.toLDTFieldModel
  intro GA GB delta h
  have hldt := strategyConsRel_consistencyDefect_le S
    _ (uniformDistribution_isProbability Unit)
    _ _ delta h
  rw [directPolynomialPolynomial_consistencyDefect_eq D S GA GB, (consistencyDefect_congr (uniformDistribution Unit)
    (fun _ => ldtPolynomialLeftPlaced D GA)
    (fun _ g => heteroKron (GA.outcome g) 1)
    (fun _ => ldtPolynomialRightPlaced D GB)
    (fun _ g => heteroKron 1 (GB.outcome g)) S.ψ
    (by intro _ g; rfl) (by intro _ g; rfl))]
  exact hldt

end

end MIPStarRE.QPBT
