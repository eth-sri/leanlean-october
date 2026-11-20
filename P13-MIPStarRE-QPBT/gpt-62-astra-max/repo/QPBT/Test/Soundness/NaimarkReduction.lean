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

variable (P : AdmissibleParams)

section

variable (S : Strategy (pauliBasisTest P))

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

variable {P} in
/-- Dilation of a Pauli basis test strategy. -/
abbrev pauliNaimarkStrategy := S.naimark

/-- The padded state is precisely the tensor image under the two fixed ground
embeddings; there is no identification of Alice's and Bob's local spaces. -/
theorem pauliNaimarkStrategy_state :
    (pauliNaimarkStrategy S).ψ =
      isometryTensor (pauliNaimarkEmbeddingA P S) (pauliNaimarkEmbeddingB P S) S.ψ :=
  (naimarkDilatedState_eq_padState _ _).symm

end

/-- A winning strategy supplies a projective setting after dilation, with no
extra premise beyond the original winning inequality. -/
def pauliNaimarkSetting (epsilon : ℝ)
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ S.value) :
    ProjectiveSetting P epsilon where
  toStrategy := pauliNaimarkStrategy S
  isProjective := S.naimark_isProjective
  win := S.naimark_value.symm ▸ hwin

section

variable (S : Strategy (pauliBasisTest P))

section

variable (w : PauliSoundnessWitness P (pauliNaimarkStrategy S))

/-- Compose a witness on the dilated strategy with the ground embeddings,
keeping both auxiliary carrier spaces and the same normalized auxiliary state. -/
@[reducible] def pauliNaimarkWitness :
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
theorem pauli_naimark_witness_state_eq :
    isometryTensor (pauliNaimarkWitness P S w).φA
        (pauliNaimarkWitness P S w).φB S.ψ =
      isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ := by
  rw [pauliNaimarkStrategy_state]
  ext p
  rw [isometryTensor_apply_eq, isometryTensor_apply_eq]
  simp only [isometryTensor_apply_eq, isometryMatrix_comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk : (isometryMatrix w.φA * isometryMatrix (pauliNaimarkEmbeddingA P S)).kronecker
        (isometryMatrix w.φB * isometryMatrix (pauliNaimarkEmbeddingB P S)) =
      (isometryMatrix w.φA).kronecker (isometryMatrix w.φB) *
        (isometryMatrix (pauliNaimarkEmbeddingA P S)).kronecker (isometryMatrix (pauliNaimarkEmbeddingB P S)) :=
    Matrix.mul_kronecker_mul _ _ _ _
  rw [hk, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

end

end

end

end MIPStarRE.QPBT
