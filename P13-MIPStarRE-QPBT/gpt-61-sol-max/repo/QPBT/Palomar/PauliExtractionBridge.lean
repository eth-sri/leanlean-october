module

public import QPBT.Palomar.ExtractionBridge
public import QPBT.Palomar.PauliExtraction
public import QPBT.Palomar.PauliGameStrategyBridge

/-!
# Exact bridges for compact Pauli extraction quantities

This module identifies the compact Pauli parameter record, prescribed-answer
effects, ideal projectors, witnesses, and extraction errors with the registered
QPBT definitions.  Every comparison is an equality; no quantitative estimate
or soundness assumption is introduced here.

The legacy import form is required because the registered soundness modules
have not yet been converted to Lean's module system.

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
      S.IsSPCC (pauliSymmetricGame P) := by classical simp_all only [ SymmetricStrategy.IsPauliSPCC, SymmetricStrategy.IsSPCC, pauliGame, pauliSymmetricGame_toGame]

variable {P : PauliParams} {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}

/-- Convert a registered qudit soundness witness to the compact strategy. -/
def ExtractionWitness.ofPauliSoundnessWitness

    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    ExtractionWitness (R := PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

variable (w : MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S))

/-- Convert a registered qubit soundness witness to the compact strategy. -/
def ExtractionWitness.ofQubitSoundnessWitness

     :
    ExtractionWitness (R := QubitRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).basisDim) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- The compact qudit state error is exactly the registered unsquared state error. -/
@[simp] theorem stateError_ofPauliSoundnessWitness

    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    stateError (ExtractionWitness.ofPauliSoundnessWitness w) =
      ‖MIPStarRE.QPBT.isometryTensor w.φA w.φB
          (pauliStrategyToLibrary P.toAdmissibleParams S).ψ -
        MIPStarRE.QPBT.idealState P.toAdmissibleParams w.aux‖ :=
  rfl

/-- The compact qubit state error is exactly the registered unsquared state error. -/
@[simp] theorem stateError_ofQubitSoundnessWitness

     :
    stateError (ExtractionWitness.ofQubitSoundnessWitness w) =
      ‖MIPStarRE.QPBT.isometryTensor w.φA w.φB
          (pauliStrategyToLibrary P.toAdmissibleParams S).ψ -
        MIPStarRE.QPBT.idealQubitState P.toAdmissibleParams w.aux‖ :=
  rfl

/-- Alice's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliAliceError_ofPauliSoundnessWitness

    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawPauliAliceError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (MIPStarRE.QPBT.fixedBinTrace
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceA P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliBobError_ofPauliSoundnessWitness

    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawPauliBobError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (MIPStarRE.QPBT.fixedBinTrace
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceB P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Alice's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitAliceError_ofQubitSoundnessWitness

     (W : PauliKind) :
    rawQubitAliceError P S (ExtractionWitness.ofQubitSoundnessWitness w)
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      MIPStarRE.QPBT.qubitOperatorDistanceA P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitBobError_ofQubitSoundnessWitness

     (W : PauliKind) :
    rawQubitBobError P S (ExtractionWitness.ofQubitSoundnessWitness w)
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      MIPStarRE.QPBT.qubitOperatorDistanceB P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

end

end MIPStarRE.QPBT.Palomar
