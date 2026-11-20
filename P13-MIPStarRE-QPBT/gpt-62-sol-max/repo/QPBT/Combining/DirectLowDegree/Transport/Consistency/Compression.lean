module

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
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Seed-fiber identities -/

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf
    (L : LdParams) (u : LdPoint L)
    (residue : SeedResidue L) :
    seededLdQuestion L
        (directLdPointQuestionOf L.toDirectLdParams u) residue =
      ldPointQuestionOf L u :=
  rfl

private theorem seedFiberPointMeasurement
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
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
  rw [matrixMeasurementTransport_postprocess,
    seededLdQuestion_directLdPointQuestionOf]
  congr 1
  funext a
  cases a <;> rfl

section

variable (L : LdParams) (S : Strategy (ldGame L))
    (u : LdPoint L)
include L S u

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA :
    (((ldStrategyToDirect L S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  exact seedFiberPointMeasurement L S.A u

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Bob's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementB :
    (((ldStrategyToDirect L S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) := by
  exact seedFiberPointMeasurement L S.B u

end

section

variable {iotaA iotaB block : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (phi : EuclideanSpace ℂ ((iotaA × block) × (iotaB × block)))
    (hphi : ∀ i j r s, phi ((i, r), (j, s)) =
      if r = s then
        psi (i, j) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹
      else 0)
include iotaA iotaB block psi phi hphi

private theorem correlatedState_compress_left
    (A : Op (iotaA × block)) (B : Op iotaB) :
    DistanceCalculus.stateQForm phi
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm psi
        (heteroKron (averageDiagonalBlock A) B) := by
  rw [correlatedState_blockDiagonal_right psi phi hphi]
  have hk (c : ℝ) (C : Op iotaA) : heteroKron (c • C) B = c • heteroKron C B :=
    Matrix.smul_kronecker c C B
  simp only [averageDiagonalBlock_apply, hk, stateQForm_real_smul,
    heteroKron_finset_sum_left, stateQForm_finset_sum]

private theorem correlatedState_compress_right
    (A : Op iotaA) (B : Op (iotaB × block)) :
    DistanceCalculus.stateQForm phi
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm psi
        (heteroKron A (averageDiagonalBlock B)) := by
  have h := correlatedState_compress_left
    (reindexState (Equiv.prodComm _ _) psi) (reindexState (Equiv.prodComm _ _) phi)
    (fun i j r s => by
      change phi ((j, s), (i, r)) = if r = s then
        psi (j, i) * (Real.sqrt (Fintype.card block : ℝ) : ℂ)⁻¹ else 0
      rw [hphi j i s r]
      simp [eq_comm]) B A
  simpa only [DistanceCalculus.stateQForm_reindexState, reindexOp_prodComm_heteroKron] using h

end

section

variable {G : Game} (S : Strategy G) (L : LdParams)
include G S L

/-- Compressing Alice's ancillary register preserves every correlation against
an operator on Bob's original carrier. -/
theorem seedFiberLiftedState_compress_left
    (A : Op (S.ιA × SeedResidue L)) (B : Op S.ιB) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  letI : Nonempty (SeedResidue L) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_left S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

/-- Compressing Bob's ancillary register preserves every correlation against
an operator on Alice's original carrier. -/
theorem seedFiberLiftedState_compress_right
    (A : Op S.ιA) (B : Op (S.ιB × SeedResidue L)) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  letI : Nonempty (SeedResidue L) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply correlatedState_compress_right S.ψ (seedFiberLiftedState S L)
  intro i j r s
  exact seedFiberLiftedState_apply S L i j r s

section

variable {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X)
include X alpha mu

/-- Compressing an arbitrary Alice family preserves its defect against a Bob
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_left
    (A : X → alpha → Op (S.ιA × SeedResidue L))
    (B : X → alpha → Op S.ιB) :
    consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  simp only [consistencyDefect, DistanceCalculus.placed_product_stateQForm_eq, seedFiberLiftedState_compress_left]

/-- Compressing an arbitrary Bob family preserves its defect against an Alice
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_right (A : X → alpha → Op S.ιA)
    (B : X → alpha → Op (S.ιB × SeedResidue L)) :
    consistencyDefect mu
        (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  simp only [consistencyDefect, DistanceCalculus.placed_product_stateQForm_eq, seedFiberLiftedState_compress_right]

end

end

/-- The point-on-Alice/global-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_pointPolynomial_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GB : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιB × SeedResidue L)) :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => ((ldStrategyToDirect L S).A
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams))
        (fun u => GB.postprocess (evalDirectPolyTupleAt u))
        (ldStrategyToDirect L S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L))
        (fun u => (seedFiberCompressPolyMeasTuple L GB).postprocess
            (evalPolyTupleAt u)) S.ψ := by
  simp (config := { dsimp := false }) only [bipartiteDefect,
    seedFiberCompressPolyMeasTuple_evaluation, seedFiberCompressMeasurement_effect,
    ldStrategyToDirect_pointMeasurementA,
    blockDiagonalMeasurement_effect]
  exact consistencyDefect_seedFiber_compress_right S L
    (uniformDistribution (LdPoint L)) _ _

/-- The global-on-Alice/point-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_polynomialPoint_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GA : DirectPolyMeasTuple L.toDirectLdParams
      (S.ιA × SeedResidue L)) :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => GA.postprocess (evalDirectPolyTupleAt u))
        (fun u => ((ldStrategyToDirect L S).B
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams))
        (ldStrategyToDirect L S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (seedFiberCompressPolyMeasTuple L GA).postprocess
            (evalPolyTupleAt u))
        (fun u => (S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)) S.ψ := by
  simp (config := { dsimp := false }) only [bipartiteDefect,
    seedFiberCompressPolyMeasTuple_evaluation, seedFiberCompressMeasurement_effect,
    ldStrategyToDirect_pointMeasurementB,
    blockDiagonalMeasurement_effect]
  exact consistencyDefect_seedFiber_compress_left S L
    (uniformDistribution (LdPoint L)) _ _

end

end MIPStarRE.QPBT
