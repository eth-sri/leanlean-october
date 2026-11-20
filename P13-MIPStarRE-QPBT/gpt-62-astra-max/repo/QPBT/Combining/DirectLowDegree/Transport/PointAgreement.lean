module

public import QPBT.Combining.DirectLowDegree.Transport.BranchComparison
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Compression
public import QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue

/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## The point-agreement branch of the directly indexed game -/

/-- Postprocessing the associated projective measurement has the same effects
as postprocessing the original measurement. -/
private theorem projMeas_postprocess_outcome_eq
    {alpha beta iota : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (f : alpha → beta)
    (b : beta) :
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas M hM) f).outcome b =
      (M.postprocess f).effect b := by
  classical
  simp only [ProjMeas.postprocess, SubMeas.postprocess_outcome,
    matrixMeasurementToLDTProjMeas_outcome,
    MIPStarRE.Quantum.Measurement.postprocess_effect]

section

variable (D : DirectLdParams) (S : Strategy (directLdGame D))

/-- The uniform average of the rejected mass at the canonical point questions
is the point-agreement branch rejection probability. -/
private theorem avgOver_directRejectedMass_point_eq :
    avgOver (uniformDistribution (DirectPoint D))
        (fun u => directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u)) =
      directLdBranchRejectionProbability S (.point, .point) := by
  let f : _ → ℝ := fun p =>
    directRejectedMass D S (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p)
  calc _
      = avgOver (uniformDistribution ((DirectPoint D) × Fin D.m))
          (fun pi => f pi.1) := (avgOver_uniform_fst f).symm
    _ = _ :=
        (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D)
          (fun pi => f pi.1)).symm
    _ = _ := by
        apply avgOver_congr
        intro sample
        rfl

/-- One of the nine ordered type branches carries at most nine times the
uniformly weighted rejection probability. -/
private theorem directLdBranchRejectionProbability_le_nine_mul
    (types : LdType × LdType) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    directLdBranchRejectionProbability S types ≤ 9 * ε := by
  have hsum : directLdRejectionProbability S =
      _⁻¹ *
        ∑ t : LdType × LdType, _ :=
    avgOver_uniform_eq_inv_card_mul_sum _
  simp [show Fintype.card LdType = 3 from by decide] at hsum
  have hsingle :=
    Finset.single_le_sum
      (fun t _ => directLdBranchRejectionProbability_nonneg D S t)
      (Finset.mem_univ types)
  have hrej : directLdRejectionProbability S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- The two point readouts of a projective direct strategy of value at least
`1 - ε` are consistent up to `9 ε` on a uniformly random point.

The direct game accepts the point-agreement branch only for equal point
answers, so the off-diagonal Born mass of the two readouts at a fixed point
question is at most the rejected mass there; averaging over the common direct
sample turns this into the point-agreement branch rejection probability, which
is at most nine times the uniformly weighted rejection because the nine
ordered type branches carry equal weight.  Blueprint
`ch13_qpbt_test.tex:137-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
theorem directLdPointPair_consistencyDefect_le (hS : S.IsProjective)
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    bipartiteDefect (uniformDistribution (DirectPoint D))
        (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D))
        (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)) S.ψ ≤ 9 * ε := by
  classical
  let PA : (DirectPoint D) →
      ProjMeas (Fin D.k → DirectScalarQ D) S.ιA := fun u =>
    ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas _
        (hS.1 (directLdPointQuestionOf D u)))
      (directLdPointValuesOrZero D)
  let PB : (DirectPoint D) →
      ProjMeas (Fin D.k → DirectScalarQ D) S.ιB := fun u =>
    ProjMeas.postprocess
      (matrixMeasurementToLDTProjMeas _
        (hS.2 (directLdPointQuestionOf D u)))
      (directLdPointValuesOrZero D)
  have hpoint : ∀ u : DirectPoint D,
      qBipartiteConsDefect (strategyQuantumState S)
          (PA u).toSubMeas (PB u).toSubMeas ≤
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u) := by
    intro u
    exact qBipartiteConsDefect_le_directRejectedMass D S hS
      _ _
      _ _
      (fun a b hab => (by
                        cases a with
                        | pointVals u =>
                            cases b with
                            | pointVals v =>
                                have huv : u = v := by
                                  simpa [directLdWinPredicate, directLdPointQuestionOf,
                                    validDirectLdAnswer] using hab
                                subst huv
                                rfl
                            | alinePolys _ =>
                                simp [directLdWinPredicate, directLdPointQuestionOf,
                                  validDirectLdAnswer] at hab
                            | dlinePolys _ =>
                                simp [directLdWinPredicate, directLdPointQuestionOf,
                                  validDirectLdAnswer] at hab
                        | alinePolys _ =>
                            simp [directLdWinPredicate, directLdPointQuestionOf,
                              validDirectLdAnswer] at hab
                        | dlinePolys _ =>
                            simp [directLdWinPredicate, directLdPointQuestionOf,
                              validDirectLdAnswer] at hab))
  have hfinal := strategyConsRel_consistencyDefect_le S
    (uniformDistribution (DirectPoint D))
    (uniformDistribution_isProbability _) PA PB _ (by
      constructor
      unfold bipartiteConsError
      calc _
          ≤ avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
              (fun u => directRejectedMass D S (directLdPointQuestionOf D u)
                (directLdPointQuestionOf D u)) := avgOver_mono _ _ _ hpoint
        _ = directLdBranchRejectionProbability S (.point, .point) :=
            avgOver_directRejectedMass_point_eq D S
        _ ≤ 9 * ε :=
            directLdBranchRejectionProbability_le_nine_mul D S _ ε hwin)
  refine le_trans (le_of_eq ?_) hfinal
  refine consistencyDefect_congr _ _ _ _ _ S.ψ (fun u a => ?_) (fun u a => ?_) <;> rw [projMeas_postprocess_outcome_eq]

end

/-! ## Transport through the correlated seed-residue dilation -/

/-- The diagonal-block average of a block-diagonal amplification is the
amplified operator.  Formalization-only support for the seed-residue
compression of `Transport.Consistency.Compression`. -/
theorem averageDiagonalBlock_blockDiagonal_const
    {iota block : Type*} [Fintype iota]
    [Fintype block] [DecidableEq block] [Nonempty block] (M : Op iota) :
    averageDiagonalBlock (Matrix.blockDiagonal fun _ : block => M) = M := by
  classical
  have hsub : ∀ r : block,
      (Matrix.blockDiagonal fun _ : block => M).submatrix
        (fun i => (i, r)) (fun i => (i, r)) = M := by
    intro r
    ext i j
    simp
  have hcard : ((Fintype.card block : ℝ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero)
  unfold averageDiagonalBlock
  simp only [hsub, Finset.sum_const, Finset.card_univ]
  simp [← Nat.cast_smul_eq_nsmul ℝ]

variable (L : LdParams) (S : Strategy (ldGame L))

/-- The point-readout consistency defect of the correlated seed-residue
dilation is exactly that of the original seed-indexed strategy.  Both point
measurements of the dilation are block-diagonal amplifications, so compressing
one of the two correlated ancillas leaves the other one's amplification to be
averaged back to itself. -/
theorem ldStrategyToDirect_pointPair_compression :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => ((ldStrategyToDirect S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams))
        (fun u => ((ldStrategyToDirect S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams))
        (ldStrategyToDirect S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (S.A (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L))
        (fun u => (S.B (ldPointQuestionOf L u)).postprocess
        (ldPointValuesOrZero L)) S.ψ := by
  let effectAt u :=
    ((S.A (ldPointQuestionOf L u)).postprocess
      (ldPointValuesOrZero L)).effect
  classical
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hA : ∀ (u : LdPoint L) (a : Fin L.k → ScalarQ L),
      (((ldStrategyToDirect S).A
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams)).effect a =
        Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
          ((S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a := by
    intro u a
    rw [ldStrategyToDirect_pointMeasurementA, blockDiagonalMeasurement_effect]
  have hB : ∀ (u : LdPoint L) (a : Fin L.k → ScalarQ L),
      (((ldStrategyToDirect S).B
        (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
          (directLdPointValuesOrZero L.toDirectLdParams)).effect a =
        Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
          ((S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)).effect a := by
    intro u a
    rw [ldStrategyToDirect_pointMeasurementB, blockDiagonalMeasurement_effect]
  calc _
      = consistencyDefect (uniformDistribution (LdPoint L))
          (fun u a => heteroKron
            (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
              effectAt u a) 1)
          (fun u a => heteroKron 1
            (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
              ((S.B (ldPointQuestionOf L u)).postprocess
                (ldPointValuesOrZero L)).effect a))
          (seedFiberLiftedState S L) :=
        consistencyDefect_congr _ _ _ _ _ (seedFiberLiftedState S L)
          (fun u a => by simp_all; rfl) (fun u a => by simp_all; rfl)
    _ = consistencyDefect (uniformDistribution (LdPoint L))
          (fun u a => heteroKron
            (effectAt u a) 1)
          (fun u a => heteroKron 1
            (averageDiagonalBlock
              (Matrix.blockDiagonal fun _ : Fin (L.q / L.m) =>
                ((S.B (ldPointQuestionOf L u)).postprocess
                  (ldPointValuesOrZero L)).effect a))) S.ψ :=
        consistencyDefect_seedFiber_compress_right S L _ _ _
    _ = _ :=
        consistencyDefect_congr _ _ _ _ _ S.ψ (fun _ _ => rfl)
          (fun _ _ => by rw [averageDiagonalBlock_blockDiagonal_const])

end

end MIPStarRE.QPBT
