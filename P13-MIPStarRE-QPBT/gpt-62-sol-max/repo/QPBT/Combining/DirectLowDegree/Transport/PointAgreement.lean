module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.GameValue
public import QPBT.Observables.WinImplications.Averages
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

/-- On the point-agreement branch an accepted pair of answers has equal
simultaneous point readouts.  This is the tuple-valued form of
`directPointAnswerReadout_eq_of_win`. -/
private theorem directLdPointValuesOrZero_eq_of_win (D : DirectLdParams)
    (p : DirectPoint D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p) a b = true) :
    directLdPointValuesOrZero D a = directLdPointValuesOrZero D b := by
  cases a <;> cases b <;>
    simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]

section

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
include D S

/-- One of the nine ordered type branches carries at most nine times the
uniformly weighted rejection probability. -/
private theorem directLdBranchRejectionProbability_le_nine_mul
    (types : LdType × LdType) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    directLdBranchRejectionProbability D S types ≤ 9 * ε := by
  have hcard : Fintype.card (LdType × LdType) = 9 := by
    rw [Fintype.card_prod, show Fintype.card LdType = 3 from by decide]
  have hsum : directLdRejectionProbability D S =
      (Fintype.card (LdType × LdType) : ℝ)⁻¹ *
        ∑ t : LdType × LdType, directLdBranchRejectionProbability D S t :=
    avgOver_uniform_eq_inv_card_mul_sum _
  rw [hcard] at hsum
  have hsingle : directLdBranchRejectionProbability D S types ≤
      ∑ t : LdType × LdType, directLdBranchRejectionProbability D S t :=
    Finset.single_le_sum
      (f := fun t => directLdBranchRejectionProbability D S t)
      (fun t _ => directLdBranchRejectionProbability_nonneg D S t)
      (Finset.mem_univ types)
  have hrej : directLdRejectionProbability D S ≤ ε := by
    rw [directLdRejectionProbability_eq_one_sub_value]
    linarith
  norm_num at hsum
  linarith

set_option maxHeartbeats 1000000 in
/-- The two point readouts are consistent up to `9 ε`, the loss from
selecting the point-agreement branch among the nine equally weighted branches. -/
theorem directLdPointPair_consistencyDefect_le
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    bipartiteDefect (uniformDistribution (DirectPoint D))
      (fun u => (S.A (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D))
      (fun u => (S.B (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D))
      S.ψ ≤ 9 * ε := by
  rw [WinImplications.consistencyDefect_postprocess_eq_mismatch]
  refine le_trans ?_ (directLdBranchRejectionProbability_le_nine_mul D S (.point, .point) ε hwin)
  rw [directLdBranchRejectionProbability_point_point_eq]
  apply avgOver_mono
  intro u
  rw [directRejectedMass_eq_event]
  exact outcome_event_weight_mono _ _ _ _ _ fun a b h =>
    Bool.eq_false_iff.mpr (h ∘ directLdPointValuesOrZero_eq_of_win D u a b)

end

/-! ## Transport through the correlated seed-residue dilation -/

section

variable (L : LdParams) (S : Strategy (ldGame L))
include L S

/-- The point-readout consistency defect of the correlated seed-residue
dilation is exactly that of the original seed-indexed strategy.  Both point
measurements of the dilation are block-diagonal amplifications, so compressing
one of the two correlated ancillas leaves the other one's amplification to be
averaged back to itself. -/
theorem ldStrategyToDirect_pointPair_compression :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => ((ldStrategyToDirect L S).A
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams))
        (fun u => ((ldStrategyToDirect L S).B
            (directLdPointQuestionOf L.toDirectLdParams u)).postprocess
              (directLdPointValuesOrZero L.toDirectLdParams))
        (ldStrategyToDirect L S).ψ =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L))
        (fun u => (S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)) S.ψ := by
  classical
  letI : Nonempty (SeedResidue L) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  rw [funext (ldStrategyToDirect_pointMeasurementA L S),
    funext (ldStrategyToDirect_pointMeasurementB L S)]
  simp only [bipartiteDefect,
    blockDiagonalMeasurement_effect]
  rw [show (ldStrategyToDirect L S).ψ = seedFiberLiftedState S L from rfl]
  erw [consistencyDefect_seedFiber_compress_right S L]
  simp only [averageDiagonalBlock_blockDiagonal_const]

/-- The two point readouts of a projective seed-indexed strategy of value at
least `1 - ε` are consistent up to `9 ε` on a uniformly random point.

The correlated seed-residue dilation has the same value, and its point
measurements are the block-diagonal amplifications of the original ones, so
the estimate transports back verbatim.  Blueprint
`ch13_qpbt_test.tex:137-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
theorem ldPointPair_consistencyDefect_le
    (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    bipartiteDefect (uniformDistribution (LdPoint L))
        (fun u => (S.A (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L))
        (fun u => (S.B (ldPointQuestionOf L u)).postprocess
            (ldPointValuesOrZero L)) S.ψ ≤ 9 * ε := by
  rw [← ldStrategyToDirect_pointPair_compression L S]
  refine directLdPointPair_consistencyDefect_le L.toDirectLdParams
    (ldStrategyToDirect L S) ε ?_
  rw [ldStrategyToDirect_value_eq]
  exact hwin

end

end

end MIPStarRE.QPBT
