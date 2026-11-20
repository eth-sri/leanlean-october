module

public import QPBT.Games.StateTransport
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect

/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

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

/-! ## Seed-fiber identities -/

section

variable (L : LdParams)

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf (u : LdPoint L)
    (residue : Fin (L.q / L.m)) :
    seededLdQuestion L
        (directLdPointQuestionOf L.toDirectLdParams u) residue =
      ldPointQuestionOf L u :=
  rfl

private theorem seedFiberPointMeasurement {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : LdQuestion L →
      MIPStarRE.Quantum.Measurement (LdAnswer L) iota)
    (u : LdPoint L) :
    (blockDiagonalMeasurement fun residue =>
        matrixMeasurementTransport (ldDirectAnswerEquiv L)
          (M (seededLdQuestion L
            (directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
        (directLdPointValuesOrZero L.toDirectLdParams) =
      blockDiagonalMeasurement fun _ =>
        (M (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  rw [blockDiagonalMeasurement_postprocess]
  apply congrArg blockDiagonalMeasurement
  funext residue
  simp [matrixMeasurementTransport_postprocess]
  congr 1
  funext a
  cases a <;> rfl

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA (S : Strategy (ldGame L))
    (u : LdPoint L) :
    (((ldStrategyToDirect S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := seedFiberPointMeasurement L S.A u

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Bob's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementB (S : Strategy (ldGame L))
    (u : LdPoint L) :
    (((ldStrategyToDirect S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := seedFiberPointMeasurement L S.B u

end

section

variable
    {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)

include hphi

private theorem correlatedState_compress_left
    (A : Op (iotaA × block)) (B : Op iotaB) :
    DistanceCalculus.stateQForm phi
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm psi
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  unfold applyOperatorToState heteroKron Matrix.kronecker averageDiagonalBlock
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
    Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : iotaA, ∑ r : block, ∑ j : iotaB,
        ∑ i' : iotaA, ∑ j' : iotaB,
          (starRingEnd ℂ)
              (Real.sqrt (Fintype.card block : ℝ))⁻¹ *
            (starRingEnd ℂ) (psi (i, j)) *
              (B j j' * (A (i, r) (i', r) *
                ((Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ *
                  psi (i', j'))))) =
        ∑ i : iotaA, ∑ j : iotaB, ∑ i' : iotaA,
          ∑ j' : iotaB, ∑ r : block,
            (starRingEnd ℂ) (psi (i, j)) *
              (psi (i', j') * (B j j' *
                ((Fintype.card block : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [hphi, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_mul, Matrix.submatrix,
      Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_comm] using h
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i'
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j'
  apply Fintype.sum_congr
  intro r
  ring_nf
  rw [inv_sqrt_natCast_mul_conj]
  ring

private theorem correlatedState_compress_right
    (A : Op iotaA) (B : Op (iotaB × block)) :
    DistanceCalculus.stateQForm phi
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm psi
        (heteroKron A (averageDiagonalBlock B)) := by
  have h := correlatedState_compress_left (reindexState (Equiv.prodComm _ _) psi)
    (reindexState (Equiv.prodComm _ _) phi) (fun i j r s => by
      change phi ((j, s), (i, r)) = if r = s then psi (j, i) * _ else 0
      by_cases h : r = s
      · subst s; simpa using hphi j i r r
      · simpa only [h, Ne.symm h, if_false] using hphi j i s r) B A
  simpa only [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron] using h

end

section

variable {G : Game} (S : Strategy G) (L : LdParams) {X alpha : Type*} [Fintype X] [DecidableEq X]
  [Fintype alpha] [DecidableEq alpha] (mu : Distribution X)

/-- Compressing an arbitrary Alice family preserves its defect against a Bob
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_left
    (A : X → alpha → Op (S.ιA × Fin (L.q / L.m)))
    (B : X → alpha → Op S.ιB) :
    consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  simp only [consistencyDefect, DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq,
    correlatedState_compress_left S.ψ (seedFiberLiftedState S L) (seedFiberLiftedState_apply S L)]

/-- Compressing an arbitrary Bob family preserves its defect against an Alice
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_right (A : X → alpha → Op S.ιA)
    (B : X → alpha → Op (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect mu
        (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  simp only [consistencyDefect, DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq,
    correlatedState_compress_right S.ψ (seedFiberLiftedState S L) (seedFiberLiftedState_apply S L)]

end

variable (L : LdParams) (S : Strategy (ldGame L))

/-- The point-on-Alice/global-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_pointPolynomial_compression
    (GB : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιB × Fin (L.q / L.m))) :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => ((ldStrategyToDirect S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams))
        (fun u => GB.postprocess (evalDirectPolyTupleAt u))
        (ldStrategyToDirect S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (S.A (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L))
        (fun u => (seedFiberCompressPolyMeasTuple L GB).postprocess
        (evalPolyTupleAt u)) S.ψ := by
  rw [funext (ldStrategyToDirect_pointMeasurementA L S)]
  simp only [bipartiteDefect,
    blockDiagonalMeasurement_effect, seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  apply consistencyDefect_seedFiber_compress_right

/-- The global-on-Alice/point-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_polynomialPoint_compression
    (GA : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιA × Fin (L.q / L.m))) :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => GA.postprocess (evalDirectPolyTupleAt u))
        (fun u => ((ldStrategyToDirect S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams))
        (ldStrategyToDirect S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (seedFiberCompressPolyMeasTuple L GA).postprocess
        (evalPolyTupleAt u))
        (fun u => (S.B (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)) S.ψ := by
  rw [funext (ldStrategyToDirect_pointMeasurementB L S)]
  simp only [bipartiteDefect,
    blockDiagonalMeasurement_effect, seedFiberCompressPolyMeasTuple_evaluation,
    seedFiberCompressMeasurement_effect]
  apply consistencyDefect_seedFiber_compress_left

end

end MIPStarRE.QPBT
