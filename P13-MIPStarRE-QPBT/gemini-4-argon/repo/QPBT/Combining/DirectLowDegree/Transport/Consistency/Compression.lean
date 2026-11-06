module

public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect

/-!
# Correlated-ancilla consistency compression
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf
    (L : LdParams) (u : Fin L.m → ScalarQ L)
    (residue : Fin (L.q / L.m)) :
    seededLdQuestion L
        (directLdPointQuestionOf L.toDirectLdParams u) residue =
      ldPointQuestionOf L u :=
  rfl

private theorem seedFiberPointMeasurement
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : LdQuestion L → MIPStarRE.Quantum.Measurement (LdAnswer L) iota)
    (u : Fin L.m → ScalarQ L) :
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
  rw [matrixMeasurementTransport_postprocess, seededLdQuestion_directLdPointQuestionOf]
  congr 1; funext a; cases a <;> rfl

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) :=
  seedFiberPointMeasurement L S.A u

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Bob's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementB
    (L : LdParams) (S : Strategy (ldGame L))
    (u : Fin L.m → ScalarQ L) :
    (((ldStrategyToDirect L S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (directLdPointValuesOrZero L.toDirectLdParams)) =
      blockDiagonalMeasurement fun _ =>
        (S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L) :=
  seedFiberPointMeasurement L S.B u

/-- Compressing Alice's ancillary register preserves every correlation against
an operator on Bob's original carrier. -/
theorem seedFiberLiftedState_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op (S.ιA × Fin (L.q / L.m))) (B : Op S.ιB) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron A (Matrix.blockDiagonal fun _ => B)) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron (averageDiagonalBlock A) B) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron Matrix.kronecker
    averageDiagonalBlock
  apply congrArg Complex.re
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : S.ιA, ∑ r : Fin (L.q / L.m), ∑ j : S.ιB, ∑ i' : S.ιA, ∑ j' : S.ιB,
          (starRingEnd ℂ) (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (S.ψ (i, j)) *
              (B j j' * (A (i, r) (i', r) *
                ((Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹ *
                  S.ψ (i', j'))))) =
        ∑ i : S.ιA, ∑ j : S.ιB, ∑ i' : S.ιA, ∑ j' : S.ιB, ∑ r : Fin (L.q / L.m),
          (starRingEnd ℂ) (S.ψ (i, j)) *
            (S.ψ (i', j') * (B j j' *
              ((Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ * A (i, r) (i', r)))) by
    simpa [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      map_mul, Matrix.submatrix, Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, mul_comm] using h
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun j => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun i' => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun j' => Fintype.sum_congr _ _ fun r => ?_
  ring_nf; rw [inv_sqrt_natCast_mul_conj (Fintype.card (Fin (L.q / L.m)))]; ring

/-- Compressing Bob's ancillary register preserves every correlation against
an operator on Alice's original carrier. -/
theorem seedFiberLiftedState_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    (A : Op S.ιA) (B : Op (S.ιB × Fin (L.q / L.m))) :
    DistanceCalculus.stateQForm (seedFiberLiftedState S L)
        (heteroKron (Matrix.blockDiagonal fun _ => A) B) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron A (averageDiagonalBlock B)) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron Matrix.kronecker
    averageDiagonalBlock
  apply congrArg Complex.re
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  suffices h :
      (∑ i : S.ιA, ∑ r : Fin (L.q / L.m), ∑ j : S.ιB, ∑ i' : S.ιA, ∑ j' : S.ιB,
          (starRingEnd ℂ) (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹ *
            (starRingEnd ℂ) (S.ψ (i, j)) *
              (A i i' * (B (j, r) (j', r) *
                ((Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹ *
                  S.ψ (i', j'))))) =
        ∑ i : S.ιA, ∑ j : S.ιB, ∑ i' : S.ιA, ∑ j' : S.ιB, ∑ r : Fin (L.q / L.m),
          (starRingEnd ℂ) (S.ψ (i, j)) *
            (S.ψ (i', j') * (A i i' *
              ((Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ * B (j, r) (j', r)))) by
    simpa [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
      apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      map_mul, Matrix.submatrix, Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, mul_comm] using h
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun j => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun i' => ?_
  rw [Finset.sum_comm]; refine Fintype.sum_congr _ _ fun j' => Fintype.sum_congr _ _ fun r => ?_
  ring_nf; rw [inv_sqrt_natCast_mul_conj (Fintype.card (Fin (L.q / L.m)))]; ring

/-- Compressing an arbitrary Alice family preserves its defect against a Bob
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_left
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X)
    (A : X → alpha → Op (S.ιA × Fin (L.q / L.m)))
    (B : X → alpha → Op S.ιB) :
    consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (Matrix.blockDiagonal fun _ => B x a))
        (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (averageDiagonalBlock (A x a)) 1)
        (fun x a => heteroKron 1 (B x a)) S.ψ := by
  classical
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  refine Finset.sum_congr rfl fun x _ => congrArg (_ * ·)
    (Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b => ?_)
  by_cases hab : a = b <;> simp [hab, seedFiberLiftedState_compress_left]

/-- Compressing an arbitrary Bob family preserves its defect against an Alice
family that is constant on the correlated residue register. -/
theorem consistencyDefect_seedFiber_compress_right
    {G : Game} (S : Strategy G) (L : LdParams)
    {X alpha : Type*} [Fintype X] [DecidableEq X]
    [Fintype alpha] [DecidableEq alpha]
    (mu : Distribution X) (A : X → alpha → Op S.ιA)
    (B : X → alpha → Op (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect mu
        (fun x a => heteroKron (Matrix.blockDiagonal fun _ => A x a) 1)
        (fun x a => heteroKron 1 (B x a)) (seedFiberLiftedState S L) =
      consistencyDefect mu
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (averageDiagonalBlock (B x a))) S.ψ := by
  classical
  unfold consistencyDefect avgOver
  simp_rw [DistanceCalculus.consistency_term_eq_stateQForm,
    DistanceCalculus.placed_product_stateQForm_eq]
  refine Finset.sum_congr rfl fun x _ => congrArg (_ * ·)
    (Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b => ?_)
  by_cases hab : a = b <;> simp [hab, seedFiberLiftedState_compress_right]

/-- The point-on-Alice/global-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_pointPolynomial_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GB : DirectPolyMeasTuple L.toDirectLdParams (S.ιB × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome =>
          heteroKron
            ((((ldStrategyToDirect L S).A
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((seedFiberCompressPolyMeasTuple L GB).postprocess
            (evalPolyTupleAt u)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [seedFiberCompressPolyMeasTuple_evaluation, seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_right S L
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome =>
      ((S.A (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect outcome)
    (fun u outcome => (GB.postprocess (evalDirectPolyTupleAt u)).effect outcome) using 1
  refine consistencyDefect_congr _ _ _ _ _ _ (fun u outcome => ?_) (fun _ _ => rfl)
  rw [ldStrategyToDirect_pointMeasurementA, blockDiagonalMeasurement_effect]
  congr 2

/-- The global-on-Alice/point-on-Bob defect of the correlated-residue extension
of the strategy is exactly the defect of the compressed polynomial tuple on the
original seed-indexed strategy. -/
theorem ldStrategyToDirect_polynomialPoint_compression
    (L : LdParams) (S : Strategy (ldGame L))
    (GA : DirectPolyMeasTuple L.toDirectLdParams (S.ιA × Fin (L.q / L.m))) :
    consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
        (fun u outcome =>
          heteroKron 1
            ((((ldStrategyToDirect L S).B
              (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (directLdPointValuesOrZero L.toDirectLdParams)).effect outcome))
        (ldStrategyToDirect L S).ψ =
      consistencyDefect (uniformDistribution (Fin L.m → ScalarQ L))
        (fun u outcome => heteroKron
          (((seedFiberCompressPolyMeasTuple L GA).postprocess
            (evalPolyTupleAt u)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect outcome)) S.ψ := by
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L by rfl]
  simp only [seedFiberCompressPolyMeasTuple_evaluation, seedFiberCompressMeasurement_effect]
  convert consistencyDefect_seedFiber_compress_left S L
    (uniformDistribution (Fin L.m → ScalarQ L))
    (fun u outcome => (GA.postprocess (evalDirectPolyTupleAt u)).effect outcome)
    (fun u outcome =>
      ((S.B (ldPointQuestionOf L u)).postprocess (ldPointValuesOrZero L)).effect outcome) using 1
  refine consistencyDefect_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun u outcome => ?_)
  rw [ldStrategyToDirect_pointMeasurementB, blockDiagonalMeasurement_effect]
  congr 2

end

end MIPStarRE.QPBT
