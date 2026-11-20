module

public import QPBT.Extraction.SwappedConsistency
public import QPBT.Extraction.EvaluatedPauliConsistency
public import QPBT.Extraction.PauliComparison

/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Simultaneous unitary conjugation preserves the quadratic form of a product. -/
theorem stateQForm_conjBy_mul_apply {I : Type*} [Fintype I] [DecidableEq I]
    (U A B : Op I) (hU : Uᴴ * U = 1) (psi : EuclideanSpace ℂ I) :
    stateQForm (applyOperatorToState U psi) (conjBy U A * conjBy U B) =
      stateQForm psi (A * B) := by
  rw [← stateQForm_conjTranspose_mul_mul]
  congr 1
  simp only [conjBy]
  grind only

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (S : ProjectiveSetting P epsilon)

section

variable (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind)
include w side W

/-- The total Pauli POVM extended to the full local extraction block and
conjugated by the concrete swap. This is the measurement in `eq:qld-unitary-7`. -/
def swappedPauliMeas : Measurement (PauliRegister P) (ExtractionBlock P (S.LocalSpace side)) :=
  Measurement.ofSumEqOne
    (fun h => conjBy (swapUnitary w side) (S.onPlayer side ((S.pauliMeas side W).effect h)))
    (fun h => by
      apply star_right_conjugate_nonneg
      exact kronecker_nonneg
        (kronecker_nonneg ((S.pauliMeas side W).pos h) Matrix.PosSemidef.one.nonneg)
        Matrix.PosSemidef.one.nonneg)
    (by
      simp only [conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
        ← heteroKron_finset_sum_left, (S.pauliMeas side W).sum_eq_one,
        heteroKron_one_one, Matrix.mul_one, swapUnitary_mul_conjTranspose])

/-- Coarse-graining commutes with extending and conjugating the Pauli POVM. -/
theorem swappedPauliMeas_eval_effect (u : PauliPoint P)
    (a : PauliScalar P) :
    ((S.swappedPauliMeas w side W).postprocess
      (fun h => evalPoly (encodingPoly h) u)).effect a =
      conjBy (swapUnitary w side) (S.onPlayer side ((S.pauliEvalMeas side W u).effect a)) := by
  simp only [swappedPauliMeas, Measurement.postprocess_effect, Measurement.ofSumEqOne,
    pauliEvalMeas, conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
    ← heteroKron_finset_sum_left]
  rfl

end

/-- Original-player placement agrees with extension to the whole local block. -/
theorem placeSide_onPlayer (side : PlayerSide) (A : Op (S.LocalSpace side)) :
    S.placeSide side (S.onPlayer side A) = S.placePlayer side A := by
  cases side
  · exact S.placeSide_alice_tensor_one _
  · exact S.placeSide_bob_tensor_one _

/-- Block placement preserves conjugation. -/
theorem placeSide_conjBy (side : PlayerSide)
    (U A : Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (conjBy U A) = conjBy (S.placeSide side U) (S.placeSide side A) := by
  cases side <;>
    simp only [placeSide, conjBy, ← reindexOp_conjTranspose,
      ← reindexOp_mul, heteroKron_conjTranspose,
      heteroKron_mul, Matrix.conjTranspose_one, Matrix.mul_one] <;> rfl

section

variable (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind)
include w side W

/-- Conjugated total-Pauli effects in block coordinates give exactly the
six-register operators required by the extraction witness. -/
theorem placeSide_swappedPauliMeas (h : PauliRegister P) :
    S.placeSide side ((S.swappedPauliMeas w side W).effect h) =
      S.swapPauliOp w side W h := by
  exact (S.placeSide_conjBy side _ _).trans
    (congrArg (conjBy (S.placeSide side (swapUnitary w side))) (S.placeSide_onPlayer side _))

/-- The evaluated canonical block measurement is the swap-conjugated
pulled-apart measurement, by `eq:qld-unitary-6`. -/
theorem canonical_eval_eq_conj_tildeM (u : PauliPoint P)
    (a : PauliScalar P) :
    ((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace side)
      (pauliRegisterMeas (params := P) W)).postprocess
      (fun h => evalPoly (encodingPoly h) u)).effect a =
      conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) := by
  rw [swapUnitary_conj_tildeM]
  simp only [Measurement.postprocess_effect, rightPlacedMeasurement_effect,
    Measurement.ofSumEqOne, pauliRegisterMeas, bracketOp, ← heteroKron_finset_sum_right]
  rfl

end

/-- The two blocks, ordered with the indicated player first. -/
def orientedBlocks : (side : PlayerSide) → S.ExpandedSpace ≃
    ExtractionBlock P (S.LocalSpace side) × ExtractionBlock P (S.LocalSpace side.other)
  | .alice => sixRegExtractionEquiv P _ _
  | .bob => (sixRegExtractionEquiv P _ _).trans (Equiv.prodComm _ _)

section

variable (side : PlayerSide)
    (A : Op (ExtractionBlock P (S.LocalSpace side)))
include side A

/-- Multiplying the two block placements gives the tensor product in the
corresponding block order. -/
theorem reindexOp_orientedBlocks_kron
    (B : Op (ExtractionBlock P (S.LocalSpace side.other))) :
    reindexOp (S.orientedBlocks side) (heteroKron A B) =
      S.placeSide side A * S.placeSide side.other B := by
  cases side <;> simp only [orientedBlocks, reindexOp_trans, reindexOp_prodComm_heteroKron,
    PlayerSide.other, placeSide, ← reindexOp_mul]
  all_goals erw [heteroKron_mul, mul_one, one_mul]

/-- The first player's operator in ordered block coordinates. -/
theorem reindexOp_orientedBlocks_left :
    reindexOp (S.orientedBlocks side) (heteroKron A 1) = S.placeSide side A := by
  cases side
  · rfl
  · simp_all [orientedBlocks, placeSide, reindexOp_trans, reindexOp_prodComm_heteroKron]

end

/-- Exact unitary transport of the evaluated overlap in either block order. -/
theorem swapped_pauli_overlap (w : GlobalPairWitness S deltaG) (side : PlayerSide) (W : PauliKind) :
    avgOver (uniformDistribution (PauliPoint P)) (fun u =>
      ∑ a : PauliScalar P, stateQForm
        (reindexState (S.orientedBlocks side)
          (S.swappedState w))
        (heteroKron (((S.swappedPauliMeas w side W).postprocess
          (fun h => evalPoly (encodingPoly h) u)).effect a)
          (((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace side.other)
            (pauliRegisterMeas (params := P) W)).postprocess
            (fun h => evalPoly (encodingPoly h) u)).effect a))) =
      1 - S.evaluatedPauliDefect w side W := by
  rw [evaluatedPauliDefect, consistencyDefect_eq_one_sub_overlap _ _ _ _
    (uniformDistribution_isProbability _) S.psiHat_norm, sub_sub_cancel]
  simp only [swappedPauliMeas_eval_effect]
  simp_rw [S.canonical_eval_eq_conj_tildeM w side.other]
  refine avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_
  rw [DistanceCalculus.stateQForm_reindexState, S.reindexOp_orientedBlocks_kron]
  erw [← S.conjBy_placeBoth_swap_placeSide w side,
    ← S.conjBy_placeBoth_swap_placeSide w side.other]
  simp only [blockMeasurement_effect, playerMeasurement_effect, ← S.placeSide_onPlayer]
  exact stateQForm_conjBy_mul_apply _ _ _ (S.placeBoth_swap_left_unitary w) S.psiHat

end ProjectiveSetting

end

end MIPStarRE.QPBT
