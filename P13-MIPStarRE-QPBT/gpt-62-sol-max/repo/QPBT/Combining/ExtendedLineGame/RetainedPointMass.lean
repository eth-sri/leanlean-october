module

public import QPBT.Combining.ExtendedLineGame.WrongVariableMass
public import QPBT.Combining.RetainedPointBounds

/-!
# Retained point mismatch on the faithful combining image

The outcome sum ranges over the actual bounded polynomial-pair embedding.
The projected vectors and both heterogeneous placements are preserved.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
include P ε S p1 p2

/-- The retained point mismatch is the squared norm of the incorrect point
projection on the actual vector `R_g psiHat`, averaged over the point. -/
def retainedPointMismatch
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) : ℝ :=
  avgOver (uniformDistribution (PauliPoint P)) (fun x =>
    ∑ pair : PolyPair P, ‖applyOperatorToState
      (1 - S.place p2 ((S.pointMeasExp p2.side W x).effect (evalAt W x pair)))
      (applyOperatorToState (S.place p1 (R.effect (directCombinedEmbedding P pair)))
        S.psiHat)‖ ^ 2)

set_option maxHeartbeats 480000 in
-- Keep the embedding comparisons folded over the polynomial outcome types.
/-- Both retained point mismatches are bounded by their appropriate full
ordered error. The wrong point projection is the outer factor: `XZ` for X,
`ZX` for Z. Normalization is used only after summing the actual vector masses,
so there is no outcome-cardinality factor. -/
theorem retainedPointMismatch_le_ordered_error (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (W : PauliKind) :
    retainedPointMismatch S p1 p2 R W ≤
      2 * extendedPolynomialOrderedError S p1 p2 R W + 4 / P.q := by
  classical
  let ψ := polyOutcomeState S p1 R
  let X := placedPoint S p2 W
  let Z := placedPoint S p2 W.other
  let A := fiberImage S p1 p2 R W
  have hmass := polyOutcomeState_norm_sum S p1 R hR
  have hretained : ∑ pair, ‖ψ (directCombinedEmbedding P pair)‖ ^ 2 ≤ 1 :=
    (sum_embedding_le _ (fun g => ‖ψ g‖ ^ 2) (fun _ => sq_nonneg _)).trans_eq hmass
  have hread (z x : PauliPoint P) (v : Fin 2 → PauliScalar P)
      (pair : PolyPair P) :
      extendedPolynomialRead P (fiberQuestionEquiv P W ((z, x), v))
        (directCombinedEmbedding P pair) =
      v 0 * evalAt W x pair +
        v 1 * evalAt W.other z pair := by
    rw [directCombinedEmbedding_read]
    cases W <;> simp [fiberQuestionEquiv, PauliKind.pairOrder, PauliKind.other, finTwoArrowEquiv, add_comm]
  have hpoint (z x : PauliPoint P) :
      (∑ pair : PolyPair P, ‖applyOperatorToState
        (1 - (X x).effect (evalAt W x pair))
          (ψ (directCombinedEmbedding P pair))‖ ^ 2) ≤
      2 * avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2) + 4 / P.q := by
    have h (pair : PolyPair P) := point_mismatch_le_ordered_error (X x) (Z z)
      (placedPoint_projective S p2 _ x) (placedPoint_projective S p2 _ z)
      (evalAt W x pair)
      (evalAt W.other z pair) (ψ (directCombinedEmbedding P pair))
    simp_rw [← hread z x] at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun pair _ => h pair)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← avgOver_sum] at hs
    refine hs.trans ?_
    rw [@FieldModel.card P.q P.model.toFieldModel, div_eq_mul_inv]
    nth_rw 2 [← mul_one (4 * (P.q : ℝ)⁻¹)]
    gcongr
    · exact avgOver_mono _ _ _ fun v =>
        sum_embedding_le (directCombinedEmbedding P) (fun g => ‖ψ g - A z x v g‖ ^ 2)
          (fun _ => sq_nonneg _)
  have hfull := fiberResidual_eq_orderedError S p1 p2 hopposite R W
  change fiberAverage P (fun z x v => ∑ g, ‖ψ g - A z x v g‖ ^ 2) = _ at hfull
  unfold fiberAverage at hfull
  have h := avgOver_mono (uniformDistribution (PauliPoint P)) _ _ fun z =>
    avgOver_mono (uniformDistribution (PauliPoint P)) _ _ (hpoint z)
  simp only [avgOver_uniform_const, avgOver_add, avgOver_const_mul, hfull] at h
  exact h

end

end

end MIPStarRE.QPBT.ExtendedLineGame
