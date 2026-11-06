module

public import QPBT.Games.MeasurementCompression
public import QPBT.Observables.Defs
public import QPBT.Test.SoundnessDefs
public import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation

/-!
# Naimark reduction for Pauli-test strategies

An arbitrary Pauli-test strategy is dilated questionwise to a projective
strategy on two separately enlarged local spaces. The ground-slice embeddings
are fixed across questions. Compression recovers both original POVM families,
including the complete Pauli-answer postprocessing. Composing any isometry
witness on the dilation with the embeddings returns its state comparison to
the original spaces. Operator-family distance transfer is not asserted here.

## References

Paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
(`thm:pauli`) and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
Blueprint `thm:pauli-naimark-reduction-support`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))

/-- The question-independent embedding of Alice's original space in the
ground slice of the completed Naimark dilation. -/
def pauliNaimarkEmbeddingA :
    EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (S.ιA × Option (PauliAnswer P)) :=
  naimarkEmbedding S.ιA (PauliAnswer P)

/-- The corresponding question-independent embedding of Bob's space. -/
def pauliNaimarkEmbeddingB :
    EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (S.ιB × Option (PauliAnswer P)) :=
  naimarkEmbedding S.ιB (PauliAnswer P)

/-- Complete the Naimark dilation separately for every question and both
players, padding the original bipartite state at the ground coordinates. -/
@[reducible] def pauliNaimarkStrategy (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) : Strategy (pauliBasisTest P) :=
  paddedStrategy S (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P))
    (fun question => dilatedMeasurement (default : PauliAnswer P) (S.A question))
    (fun question => dilatedMeasurement (default : PauliAnswer P) (S.B question))

/-- Both local families of the dilated strategy are projective measurements. -/
theorem pauliNaimarkStrategy_isProjective : (pauliNaimarkStrategy P S).IsProjective :=
  paddedStrategy_isProjective S none none _ _
    (fun question => dilatedMeasurement_isProjective
      (default : PauliAnswer P) (S.A question))
    (fun question => dilatedMeasurement_isProjective
      (default : PauliAnswer P) (S.B question))

/-- The two ground-slice compressions preserve the value of the game exactly. -/
theorem pauliNaimarkStrategy_value : (pauliNaimarkStrategy P S).value = S.value :=
  paddedStrategy_value S none none _ _
    (fun question answer => dilatedMeasurement_compression
      (default : PauliAnswer P) answer (S.A question))
    (fun question answer => dilatedMeasurement_compression
      (default : PauliAnswer P) answer (S.B question))

/-- The padded state is precisely the tensor image under the two fixed ground
embeddings; there is no identification of Alice's and Bob's local spaces. -/
theorem pauliNaimarkStrategy_state :
    (pauliNaimarkStrategy P S).ψ =
      isometryTensor (pauliNaimarkEmbeddingA P S) (pauliNaimarkEmbeddingB P S) S.ψ := by
  change padState none none S.ψ = naimarkDilatedState (PauliAnswer P) S.ψ
  ext p
  rw [naimarkDilatedState_apply]
  simp only [padState, EuclideanSpace.equiv]
  by_cases hA : p.1.2 = none <;> by_cases hB : p.2.2 = none <;> simp [hA, hB]

/-- A winning strategy supplies a projective setting after dilation, with no
extra premise beyond the original winning inequality. -/
def pauliNaimarkSetting (P : AdmissibleParams) (epsilon : ℝ)
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ S.value) :
    ProjectiveSetting P epsilon where
  toStrategy := pauliNaimarkStrategy P S
  isProjective := pauliNaimarkStrategy_isProjective P S
  win := by simp_all [pauliNaimarkStrategy_value]

/-- Compression commutes with the complete `pauliAnswerOrZero` postprocessing
of Alice's Pauli-question measurement, including wrong-form outcomes. -/
theorem pauliNaimarkStrategy_pauli_compressA (W : PauliKind) :
    (((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).compressAt none =
        (S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero := by
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]

/-- Compression commutes with the complete `pauliAnswerOrZero` postprocessing
of Bob's Pauli-question measurement, including wrong-form outcomes. -/
theorem pauliNaimarkStrategy_pauli_compressB (W : PauliKind) :
    (((pauliNaimarkStrategy P S).B (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).compressAt none =
        (S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero := by
  rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    Measurement.compressAt_dilatedMeasurement]

/-- Compose a witness on the dilated strategy with the ground embeddings,
keeping both auxiliary carrier spaces and the same normalized auxiliary state. -/
@[reducible] def pauliNaimarkWitness (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    PauliSoundnessWitness P S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  ιAFintype := w.ιAFintype
  ιBFintype := w.ιBFintype
  ιADecidableEq := w.ιADecidableEq
  ιBDecidableEq := w.ιBDecidableEq
  φA := w.φA.comp (pauliNaimarkEmbeddingA P S)
  φB := w.φB.comp (pauliNaimarkEmbeddingB P S)
  aux := w.aux
  aux_norm := w.aux_norm

/-- The extracted original state is exactly the extracted dilated state. -/
theorem pauli_naimark_witness_state_eq (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    isometryTensor (pauliNaimarkWitness P S w).φA
        (pauliNaimarkWitness P S w).φB S.ψ =
      isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ := by
  grind [pauliNaimarkStrategy_state, isometryTensor_comp]

/-- Consequently the original and dilated witnesses have equal state-distance
quantities from the same ideal auxiliary state. -/
theorem pauli_naimark_witness_state_distance_eq (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    ‖isometryTensor (pauliNaimarkWitness P S w).φA
        (pauliNaimarkWitness P S w).φB S.ψ -
      idealState P (pauliNaimarkWitness P S w).aux‖ =
    ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
      idealState P w.aux‖ := by
  rw [pauli_naimark_witness_state_eq]

end

end MIPStarRE.QPBT
