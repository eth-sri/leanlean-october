module

public import QPBT.Palomar.Bridge
public import QPBT.Palomar.Definitions
public import QPBT.Test.Soundness
public import QPBT.Algebra.PauliTheorems
public import QPBT.Palomar.PauliGameStrategyBridge

/-!
# Exact bridges for compact Pauli extraction quantities

This module identifies the compact Pauli parameter record, prescribed-answer
effects, ideal projectors, witnesses, and extraction errors with the registered
QPBT definitions.  Every comparison is an equality; no quantitative estimate
or soundness assumption is introduced here.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

attribute [local instance] compactPauliQuestionDecidableEq

/-- The compact admissibility witness has the registered named proposition. -/
theorem PauliParams.is_admissible_size (P : PauliParams) :
    MIPStarRE.QPBT.IsAdmissibleSize P.q :=
  P.hq

/-- Copy compact numerical parameters into the registered Pauli-test domain. -/
def PauliParams.toAdmissibleParams (P : PauliParams) :
    MIPStarRE.QPBT.AdmissibleParams where
  q := P.q
  m := P.m
  d := P.d
  hd := P.hd
  hq := P.is_admissible_size
  hdvd := P.hdvd

/-- The canonical field and concrete game of the compact parameter tuple. -/
abbrev PauliParams.model (P : PauliParams) := P.toAdmissibleParams.model

abbrev PauliParams.game (P : PauliParams) :=
  pauliGame P (QPBT.binaryRepresentation P.model) (QPBT.fixedBinTrace P.model)

/-- Compact parameters are recovered exactly after conversion to the library record. -/
@[simp] theorem PauliParams.ofAdmissibleParams_toAdmissibleParams (P : PauliParams) :
    PauliParams.ofAdmissibleParams P.toAdmissibleParams = P := by
  cases P
  rfl

/-- The concrete compact SPCC predicate is exactly the transported symmetric-game predicate. -/
theorem isPauliSPCC_iff_isSPCC (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricPauliStrategy (PauliParams.ofAdmissibleParams P)
      (MIPStarRE.QPBT.PauliScalar P)) :
    S.IsPauliSPCC (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) ↔
      S.IsSPCC (pauliSymmetricGame P) := by
  unfold SymmetricStrategy.IsPauliSPCC SymmetricStrategy.IsSPCC
  have hgame := congrArg Game.μ
    (pauliSymmetricGame_toGame P)
  have hmu : (pauliSymmetricGame P).μ =
      pauliQuestionPMF (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) := by
    simpa only [pauliGame] using hgame
  rw [hmu]

/-- Convert a registered qudit soundness witness to the compact strategy. -/
def ExtractionWitness.ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P P.model.K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    ExtractionWitness (R := PauliRegister P P.model.K) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- The compact qudit state error is exactly the registered unsquared state error. -/
@[simp] theorem stateError_ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P P.model.K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    stateError (ExtractionWitness.ofPauliSoundnessWitness w) =
      ‖MIPStarRE.QPBT.isometryTensor w.φA w.φB
          (pauliStrategyToLibrary P.toAdmissibleParams S).ψ -
        MIPStarRE.QPBT.idealState P.toAdmissibleParams w.aux‖ :=
  rfl

private theorem idealProjectorAlice_tensor {I J R : Type}
    [DecidableEq I] [DecidableEq J] [DecidableEq R] (M : Matrix R R ℂ) :
    idealProjectorAlice (I' := I) (J' := J) M = heteroKron (heteroKron 1 M) 1 := by
  ext p q
  simp [idealProjectorAlice, heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and, ite_mul, mul_ite] <;> split_ifs <;> rfl

private theorem idealProjectorBob_tensor {I J R : Type}
    [DecidableEq I] [DecidableEq J] [DecidableEq R] (M : Matrix R R ℂ) :
    idealProjectorBob (I' := I) (J' := J) M = heteroKron 1 (heteroKron 1 M) := by
  ext p q
  simp [idealProjectorBob, heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and, ite_mul, mul_ite] <;> split_ifs <;> rfl

section

variable {I A B R : Type}
    [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
include I A B R

private theorem liftedPauliAliceEffect_tensor (φ : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (A × R))
    (M : Matrix I I ℂ) :
    liftedPauliAliceEffect (J' := B) φ M = heteroKron (QPBT.conjIsometry φ M) 1 := by
  ext p q
  simp [liftedPauliAliceEffect, heteroKron, Matrix.kronecker, Matrix.one_apply, mul_ite,
    Palomar.conjIsometry, QPBT.conjIsometry]

private theorem liftedPauliBobEffect_tensor (φ : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (B × R))
    (M : Matrix I I ℂ) :
    liftedPauliBobEffect (I' := A) φ M = heteroKron 1 (QPBT.conjIsometry φ M) := by
  ext p q
  simp [liftedPauliBobEffect, heteroKron, Matrix.kronecker, Matrix.one_apply, ite_mul,
    Palomar.conjIsometry, QPBT.conjIsometry]

end

section

variable {P : PauliParams}
    {S : PauliStrategy P P.model.K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind)
include P S w W

/-- Alice's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliAliceError_ofPauliSoundnessWitness :
    rawPauliAliceError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (QPBT.fixedBinTrace P.model) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceA P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> simp only [rawPauliAliceError, aliceOperatorError, rawPauliOperatorDistanceA,
    liftedPauliAliceEffect_tensor, liftedAEffect, idealProjectorAlice_tensor, pauliProjOnA'',
    applyOperatorToState] <;> rfl

/-- Bob's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliBobError_ofPauliSoundnessWitness :
    rawPauliBobError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (QPBT.fixedBinTrace P.model) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceB P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> simp only [rawPauliBobError, bobOperatorError, rawPauliOperatorDistanceB,
    liftedPauliBobEffect_tensor, liftedBEffect, idealProjectorBob_tensor, pauliProjOnB'',
    applyOperatorToState] <;> rfl

end

section

variable {X Y A B R T : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R] [Nonempty R] [Fintype T] [DecidableEq T] [Nonempty T]
    {S : Strategy X Y A B} (e : R ≃ T) (w : ExtractionWitness (R := R) S)

abbrev localLabels (I : Type) := (Equiv.refl I).prodCongr e

private abbrev jointLabels := (localLabels e w.ιA').prodCongr (localLabels e w.ιB')

/-- Reindex the extracted register on each side, leaving the auxiliary state unchanged. -/
abbrev ExtractionWitness.reindex : ExtractionWitness (R := T) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (localLabels e w.ιA')).toLinearIsometry.comp w.φA
  φB := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (localLabels e w.ιB')).toLinearIsometry.comp w.φB
  aux := w.aux
  aux_norm := w.aux_norm

private theorem idealExtractionState_reindex :
    idealExtractionState (w.reindex e) = QPBT.reindexState (jointLabels e w) (idealExtractionState w) := by
  ext x
  simp [idealExtractionState, ExtractionWitness.reindex, QPBT.reindexState, normalizedEPRState, EuclideanSpace.equiv,
    ← Fintype.card_congr e] <;> rfl

/-- The state error does not change with the computational basis labels. -/
theorem stateError_reindex : stateError (w.reindex e) = stateError w := by
  unfold stateError
  rw [idealExtractionState_reindex]
  exact norm_reindexState_sub_eq (jointLabels e w) (localIsometryTensor w.φA w.φB S.ψ) (idealExtractionState w)

private theorem operatorError_reindex {O : Type} [Fintype O]
    (A B : O → Matrix ((w.ιA' × R) × (w.ιB' × R)) ((w.ιA' × R) × (w.ιB' × R)) ℂ) :
    aliceOperatorError (w.reindex e)
      (fun o => Matrix.reindex (jointLabels e w) (jointLabels e w) (A o))
      (fun o => Matrix.reindex (jointLabels e w) (jointLabels e w) (B o)) =
    aliceOperatorError w A B := by
  unfold aliceOperatorError
  rw [idealExtractionState_reindex]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  change ‖applyOperatorToState _ _‖ = ‖applyOperatorToState _ _‖
  rw [norm_applyOperatorToState_reindexState]
  congr 2
  ext i j
  simp only [reindexOp, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
    Matrix.sub_apply, Equiv.symm_apply_apply]

end

private theorem conjIsometry_reindex {I J L : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (e : J ≃ L) (φ : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J) (M : Matrix I I ℂ) :
    Matrix.reindex e e (QPBT.conjIsometry φ M) =
      conjIsometry ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry.comp φ) M := by
  ext i j
  rfl

/-- Expand a register label in the fixed binary coordinates. -/
abbrev binaryLabels (P : PauliParams) : PauliRegister P P.model.K ≃ QubitRegister P P.model.basisDim :=
  quditQubitLabelEquiv P.model

private theorem pauliProj_binary (P : PauliParams) (W : PauliKind) (u : PauliRegister P P.model.K) :
    Matrix.reindex (binaryLabels P) (binaryLabels P) (pauliProj (fixedBinTrace P.model) W u) =
      qubitPauliProj W (binaryRegisterLabel P.model.binaryCoordinates u) := by
  have h := QPBT.pauliProj_reindex_quditQubitLabelEquiv P.model (pauliKindEquiv W) u
  have h' := congrArg (Matrix.reindex (binaryLabels P) (binaryLabels P)) h
  have h'' : Matrix.reindex (binaryLabels P) (binaryLabels P) (QPBT.pauliProj (pauliKindEquiv W) u) =
      QPBT.qubitPauliProj (pauliKindEquiv W) (kappaVec P.model u) := by
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix] using h'
  cases W <;> exact h''

section

variable {P : PauliParams} {S : PauliStrategy P P.model.K}
    (w : ExtractionWitness (R := PauliRegister P P.model.K) S) (W : PauliKind)

/-- Binary reindexing preserves Alice's raw-effect error sum. -/
theorem rawQubitAliceError_reindex :
    rawQubitAliceError P S (w.reindex (binaryLabels P)) P.model.binaryCoordinates W =
      rawPauliAliceError P S w (fixedBinTrace P.model) W := by
  unfold rawPauliAliceError rawQubitAliceError
  simp only [ExtractionWitness.reindex]
  simpa only [liftedPauliAliceEffect_tensor,
    idealProjectorAlice_tensor, jointLabels, heteroKron, reindex_kronecker, matrixReindex_one,
    conjIsometry_reindex, localLabels, pauliProj_binary, liftedQubitAliceEffect,
    ExtractionWitness.reindex] using operatorError_reindex (binaryLabels P) w
      (fun u => liftedPauliAliceEffect w.φA ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
      (fun u => idealProjectorAlice (pauliProj (fixedBinTrace P.model) W u))

/-- Binary reindexing preserves Bob's raw-effect error sum. -/
theorem rawQubitBobError_reindex :
    rawQubitBobError P S (w.reindex (binaryLabels P)) P.model.binaryCoordinates W =
      rawPauliBobError P S w (fixedBinTrace P.model) W := by
  unfold rawPauliBobError rawQubitBobError
  change aliceOperatorError (w.reindex (binaryLabels P)) _ _ = aliceOperatorError w _ _
  simp only [ExtractionWitness.reindex]
  simpa only [liftedPauliBobEffect_tensor, idealProjectorBob_tensor, jointLabels, heteroKron,
    reindex_kronecker, matrixReindex_one, conjIsometry_reindex, localLabels, pauliProj_binary,
    liftedQubitBobEffect, ExtractionWitness.reindex] using operatorError_reindex (binaryLabels P) w
      (fun u => liftedPauliBobEffect w.φB ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
      (fun u => idealProjectorBob (pauliProj (fixedBinTrace P.model) W u))

end

end

end MIPStarRE.QPBT.Palomar
