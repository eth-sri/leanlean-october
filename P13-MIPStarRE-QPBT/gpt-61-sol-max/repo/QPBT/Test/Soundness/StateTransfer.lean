module

public import QPBT.Test.Soundness.Ancilla
public import QPBT.Combining.RootErrorBounds
public import QPBT.Extraction.Unitary

/-!
# State transfer from supplied extraction data

The extraction witness uses six registers, while the test conclusion groups
each player's first two registers into the auxiliary space. Adjoining the local
EPR states and applying the supplied swap unitaries gives the test isometries.
The squared state error is unchanged by this identification.

## References

Formalization support for blueprint `thm:pauli` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This module transports supplied data without invoking either existence theorem.
The companion `OperatorTransfer` module completes both operator comparisons.
The source-facing obligations are tracked by issues #529 and #586 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}

variable (v : ExtractionWitness S w delta)

/-- The local isometries and auxiliary state associated to supplied extraction
data. This is the construction in the final proof of `thm:pauli`, with the
extraction conclusion explicitly given. No existence assertion is made.
This construction is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
def ExtractionWitness.toPauliSoundnessWitness  :
    PauliSoundnessWitness P S.toStrategy where
  ιA' := S.toStrategy.ιA × PauliRegister P
  ιB' := S.toStrategy.ιB × PauliRegister P
  φA := unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
    (swapUnitary w .alice) (v.swap_left_unitary .alice)
  φB := unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
    (swapUnitary w .bob) (v.swap_left_unitary .bob)
  aux := v.aux
  aux_norm := v.aux_norm

open Classical in
/-- The two ancilla embeddings produce exactly the expanded strategy state,
after grouping the local registers as `(AA')A''` and `(BB')B''`.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem isometryTensor_ancilla_eq_psiHat (S : ProjectiveSetting P epsilon) :
    isometryTensor
        (ancillaBlockIsometry (ι := S.toStrategy.ιA)
          (eprState (PauliRegister P)) (eprState_norm _))
        (ancillaBlockIsometry (ι := S.toStrategy.ιB)
          (eprState (PauliRegister P)) (eprState_norm _)) S.toStrategy.ψ =
      reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat := by
  ext p
  simp [isometryTensor_apply_eq, ancillaBlockIsometry_matrix_apply, Matrix.kronecker,
    Fintype.sum_prod_type, ProjectiveSetting.psiHat, reindexState, vecTensor,
    sixRegExtractionEquiv, sixRegShuffle, mul_comm, mul_left_comm]

open Classical in
/-- The tensor of the constructed test isometries is the supplied simultaneous
swap action, in test register order. This identity precedes every state-error
estimate and requires no success or consistency bound.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.isometryTensor_eq  :
    isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ =
      reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat) := by
  have haction := isometryTensor_ancilla_eq_psiHat S
  change isometryTensor
    (unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
      (swapUnitary w .alice) (v.swap_left_unitary .alice))
    (unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
      (swapUnitary w .bob) (v.swap_left_unitary .bob)) S.toStrategy.ψ = _
  rw [isometryTensor_eq_toEuclideanLin]
  have hA := unitaryAncillaIsometry_matrix (eprState (PauliRegister P))
    (eprState_norm _) (swapUnitary w .alice) (v.swap_left_unitary .alice)
  have hB := unitaryAncillaIsometry_matrix (eprState (PauliRegister P))
    (eprState_norm _) (swapUnitary w .bob) (v.swap_left_unitary .bob)
  rw [hA, hB]
  rw [Matrix.kronecker, Matrix.mul_kronecker_mul, toEuclideanLin_mul_apply]
  rw [isometryTensor_eq_toEuclideanLin] at haction
  erw [haction]
  ext p
  symm
  change ((Matrix.kronecker (swapUnitary w .alice) (swapUnitary w .bob)).submatrix
      (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) *ᵥ
         S.psiHat )
      ((sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB).symm p) = _
  erw [Matrix.submatrix_mulVec_equiv]
  rfl

open Classical in
/-- The auxiliary-state/EPR vector is unchanged by grouping each player's
first two registers into that player's auxiliary space.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.idealState_eq  :
    idealState P v.toPauliSoundnessWitness.aux =
      reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.idealExpState v.aux) := by
  ext p
  rfl

open Classical in
/-- The supplied extraction state's squared error is exactly the squared state
error of its test witness. Only the register order changes.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.state_error_eq  :
    ‖isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 =
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  rw [v.isometryTensor_eq, v.idealState_eq]
  dsimp +instances only [ExtractionWitness.toPauliSoundnessWitness, ProjectiveSetting.LocalSpace,
    ProjectiveSetting.localSpaceFintype, ProjectiveSetting.localSpaceDecidableEq]
  have hsub : ∀ x y : MIPStarRE.QPBT.StateVector (SixReg P S.toStrategy.ιA S.toStrategy.ιB),
      reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) x -
        reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) y =
      reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (x - y) := by
    intros x y
    rfl
  rw [hsub, reindexState_norm_eq]

/-- Conditional transfer of the state estimate from fully supplied extraction
data. The paper-facing theorem must still construct that data; see issue
Dengnifer/MIPStarRE-QPBT-bak#529.
This is blueprint `lem:pauli-extraction-state-distance-support`. -/
theorem ExtractionWitness.state_close_ofExtractionWitness  :
    ‖isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 ≤ delta := by
  rw [v.state_error_eq]
  exact v.state_close

end

end MIPStarRE.QPBT
