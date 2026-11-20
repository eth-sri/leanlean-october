module

public import QPBT.Extraction.PauliTransport

/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (S : ProjectiveSetting P epsilon)

section

variable (side : PlayerSide)
    (aux : EuclideanSpace ℂ (S.ExtractionAux))
include side aux

/-- The auxiliary state in the same order as the local extraction blocks. -/
def orientedAux :
    EuclideanSpace ℂ (S.ExpandedLocalSpace side × S.ExpandedLocalSpace side.other) :=
  match side with
  | .alice => aux
  | .bob => reindexState (Equiv.prodComm _ _) aux

theorem orientedAux_norm :
    ‖S.orientedAux side aux‖ = ‖aux‖ := by
  cases side
  · rfl
  · exact reindexState_norm_eq _ _

theorem idealExpState_orientedBlocks :
    reindexState (S.orientedBlocks side) (S.idealExpState aux) =
      reindexState prodShuffle (vecTensor (S.orientedAux side aux) (eprState (PauliRegister P))) := by
  cases side
  · rfl
  · ext p
    simp [orientedAux, orientedBlocks, idealExpState, reindexState, vecTensor, eprState,
      extractionIdealShuffle, sixRegExtractionEquiv, prodShuffle, eq_comm]

end

/-- Subtraction of block operators agrees with subtraction after placement. -/
theorem placeSide_sub (side : PlayerSide)
    (A B : Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (A - B) = S.placeSide side A - S.placeSide side B := by
  cases side
  · ext row col
    exact sub_mul _ _ _
  · ext row col
    exact mul_sub _ _ _

section

variable (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (S.ExtractionAux))
include w aux

/-- The entire answer-summed distance in block coordinates is the distance
appearing in `ExtractionWitness.pauli_close`, for either player. -/
theorem extraction_pauli_dist_eq_sum
    (side : PlayerSide) (W : PauliKind) :
    S.swapPauliDistance w aux side W =
      ∑ h : PauliRegister P, ‖applyOperatorToState
        (S.placeSide side (((S.swappedPauliMeas w side W).effect h) -
          heteroKron (1 : Op (S.ExpandedLocalSpace side)) (pauliProj W h)))
        (S.idealExpState aux)‖ ^ 2 := by
  simp only [swapPauliDistance, S.placeSide_sub, S.placeSide_swappedPauliMeas,
    idealPauliOp, placeExtractedRegister, opFamilyDistSq, avgOver_uniform_const]

set_option maxHeartbeats 800000 in
/-- For the concrete swaps, the full Pauli distance on the normalized ideal
state is bounded by the evaluated consistency defect and the two established
comparison losses. This instantiates `eq:qld-unitary-7`--`eq:qld-unitary-9`
with all six-register placements and both player orientations. -/
theorem extraction_pauli_dist_le
    (haux : ‖aux‖ = 1) (side : PlayerSide) (W : PauliKind) :
    S.swapPauliDistance w aux side W ≤
      2 * S.evaluatedPauliDefect w side W + 2 * ((P.m * P.d : ℝ) / P.q) +
        4 * ‖S.swappedState w -
          S.idealExpState aux‖ := by
  let e := S.orientedBlocks side
  let theta := S.swappedState w
  have htheta : ‖reindexState e theta‖ = 1 := (reindexState_norm_eq _ _).trans (S.swappedState_norm w)
  have h := pauli_distance_on_ideal_le (S.swappedPauliMeas w side W) W
    (S.orientedAux side aux) ((S.orientedAux_norm side aux).trans haux) (reindexState e theta) htheta
  dsimp only at h
  erw [S.swapped_pauli_overlap w side W, sub_sub_cancel,
    ← S.idealExpState_orientedBlocks side aux, norm_reindexState_sub_eq] at h
  rw [S.extraction_pauli_dist_eq_sum]
  refine (le_of_eq (Finset.sum_congr rfl fun g _ => ?_)).trans h
  rw [← S.reindexOp_orientedBlocks_left side]
  exact congrArg (· ^ 2) (norm_applyOperatorToState_reindexState (S.orientedBlocks side) _ _).symm

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
