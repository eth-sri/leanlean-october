module

public import QPBT.Games.StrategyClasses
public import QPBT.Test.MagicSquareTheorems.Rigidity.Relations

/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## The ground slice of an enlarged local space -/

/-- The linear map sending a vector `x` of `ℂ^ι` to `x ⊗ |⊥⟩`, where `|⊥⟩` is the
basis vector of the auxiliary register `ℂ^{Option α}` indexed by the adjoined
point.  Formalization-only support for the dilation used by blueprint
`thm:ms-rigidity`. -/
def naimarkEmbeddingMap (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ι × Option α) where
  toFun x := (EuclideanSpace.equiv (ι × Option α) ℂ).symm
    (fun p => if p.2 = none then x p.1 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.2 = none <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.2 = none <;> simp [h]

/-- The isometric identification of a local Hilbert space `ℂ^ι` with the *ground
slice* `ℂ^ι ⊗ |⊥⟩` of the enlarged space `ℂ^{ι × Option α}`.  This single
embedding serves every question of the dilation supporting blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def naimarkEmbedding (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × Option α) :=
  LinearMap.isometryOfInner (naimarkEmbeddingMap ι α) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, naimarkEmbeddingMap]

/-- The coordinates of the ground embedding: the amplitude is carried to the
auxiliary basis vector `|⊥⟩` and vanishes on the other auxiliary vectors. -/
@[simp]
theorem naimarkEmbedding_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (x : EuclideanSpace ℂ ι) (p : ι × Option α) :
    naimarkEmbedding ι α x p = if p.2 = none then x p.1 else 0 := rfl

/-- The compression of an operator on the enlarged space to the ground slice.
Formalization-only support for the dilation of blueprint
`thm:ms-rigidity`. -/
def naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op (ι × Option α)) : Op ι :=
  M.submatrix (fun i => (i, none)) (fun j => (j, none))

/-- The entries of the ground-slice compression. -/
@[simp]
theorem naimarkCompression_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op (ι × Option α)) (i j : ι) :
    naimarkCompression (α := α) M i j = M (i, none) (j, none) := rfl

/-- The operator on the enlarged space that acts as `M` on the ground slice and
annihilates its orthogonal complement.  Formalization-only support for the
dilation of blueprint `thm:ms-rigidity`. -/
def naimarkInflation {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) : Op (ι × Option α) :=
  Matrix.of fun p q => if p.2 = none ∧ q.2 = none then M p.1 q.1 else 0

/-- The entries of the inflation of an operator to the enlarged space. -/
@[simp]
theorem naimarkInflation_apply {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) (p q : ι × Option α) :
    naimarkInflation (α := α) M p q =
      if p.2 = none ∧ q.2 = none then M p.1 q.1 else 0 := rfl

/-! ## The dilated state -/

section

variable (α : Type) [Fintype α] [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
  [Fintype ιB] [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- The image of a bipartite state under the two ground embeddings.  This is the
state of the dilated strategy supporting blueprint
`thm:ms-rigidity`. -/
noncomputable def naimarkDilatedState :
    EuclideanSpace ℂ ((ιA × Option α) × (ιB × Option α)) :=
  isometryTensor (naimarkEmbedding ιA α) (naimarkEmbedding ιB α) ψ

/-- The coordinates of the dilated state: the original amplitudes sit on the
ground slice, where both auxiliary registers carry the adjoined basis vector,
and all remaining coordinates vanish. -/
theorem naimarkDilatedState_apply (p : (ιA × Option α) × (ιB × Option α)) :
    naimarkDilatedState α ψ p =
      if p.1.2 = none ∧ p.2.2 = none then ψ (p.1.1, p.2.1) else 0 := by
  classical
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  simp [naimarkDilatedState, isometryTensor]
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp_all
    · simp [hob]
  · simp [hoa]

/-- Ground embedding is the coordinate padding used by the generic dilation. -/
theorem naimarkDilatedState_eq_padState :
    naimarkDilatedState α ψ = padState (none : Option α) none ψ := by
  ext ⟨⟨i, a⟩, j, b⟩
  cases a <;> cases b <;> simp [padState, naimarkDilatedState_apply]

theorem naimarkDilatedState_norm : ‖naimarkDilatedState α ψ‖ = ‖ψ‖ := by
  rw [naimarkDilatedState_eq_padState, padState_norm]

end

/-! ## The dilated Magic Square strategy -/

section

variable (S : Strategy msGame)

/-- The projective dilation of an arbitrary Magic Square strategy.  Both local
spaces acquire one auxiliary register indexed by `Option MsAnswer`, the state is
carried to the ground slice, and each question measurement is replaced by its
Naimark dilation, the deficiency being absorbed by the answer `bit 0`.  This is
the projective strategy on which the self-testing argument of `thm:ms-rigidity`
operates; blueprint `thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msDilatedStrategy : Strategy msGame where
  ιA := S.ιA × Option MsAnswer
  ιB := S.ιB × Option MsAnswer
  ψ := naimarkDilatedState MsAnswer S.ψ
  ψ_norm := (naimarkDilatedState_norm _ _).trans S.ψ_norm
  A x := dilatedMeasurement (MsAnswer.bit 0) (S.A x)
  B y := dilatedMeasurement (MsAnswer.bit 0) (S.B y)

/-- Every question measurement of the dilated strategy is projective, which is
the hypothesis under which the Coladangelo--Stark self-test is stated. -/
theorem msDilatedStrategy_isProjective_A (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective ((msDilatedStrategy S).A x) :=
  dilatedMeasurement_isProjective _ (S.A x)

/-- Every question measurement of the dilated strategy is projective on Bob's
side as well. -/
theorem msDilatedStrategy_isProjective_B (y : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective ((msDilatedStrategy S).B y) :=
  dilatedMeasurement_isProjective _ (S.B y)

/-! ## Preservation of the value-to-parity layer -/

/-- The dilation preserves every conditioned Born mass. -/
theorem ms_dilated_strategy_outcome_weight (x y : MsType)
    (a b : MsAnswer) :
    outcomeWeight (msDilatedStrategy S) x y a b = outcomeWeight S x y a b := by
  change vectorQForm (naimarkDilatedState MsAnswer S.ψ) _ = _
  rw [naimarkDilatedState_eq_padState]
  exact stateQForm_padState _ _ _ _ _ _ _
    (dilatedMeasurement_compression _ a (S.A x)) (dilatedMeasurement_compression _ b (S.B y))

/-- The dilation preserves Alice's marginal Born masses. -/
theorem ms_dilated_strategy_alice_outcome_weight (x : MsType)
    (a : MsAnswer) :
    aliceOutcomeWeight (msDilatedStrategy S) x a = aliceOutcomeWeight S x a := by
  rw [← sum_outcome_weight_right,
    ← sum_outcome_weight_right]
  exact Finset.sum_congr rfl fun b _ => ms_dilated_strategy_outcome_weight S x x a b

/-- The dilation preserves the mass of every answer event. -/
theorem ms_dilated_strategy_outcome_event_weight (x y : MsType)
    (E : MsAnswer → MsAnswer → Prop) [DecidableRel E] :
    outcomeEventWeight (msDilatedStrategy S) x y E = outcomeEventWeight S x y E := by
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    by_cases h : E a b <;> simp [h, ms_dilated_strategy_outcome_weight]

/-- The dilation preserves the mass of every event depending only on Alice's
answer. -/
theorem ms_dilated_strategy_alice_event_weight (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] :
    aliceEventWeight (msDilatedStrategy S) x E = aliceEventWeight S x E := by
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : E a <;> simp [h, ms_dilated_strategy_alice_outcome_weight]

/-- The dilation preserves the forward cell-consistency defect. -/
theorem ms_dilated_strategy_forward_cell_mismatch_mass
    (i : Fin 6) (k : Fin 3) :
    forwardCellMismatchMass (msDilatedStrategy S) i k = forwardCellMismatchMass S i k :=
  ms_dilated_strategy_outcome_event_weight S _ _ _

end

/-! ## Composition of the dilation with later local isometries -/

/-- The matrix of a linear isometry of Euclidean spaces in the computational
bases.  Formalization-only support for blueprint
`thm:ms-rigidity`. -/
noncomputable def isometryMatrix {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') : Matrix ι' ι ℂ :=
  Matrix.toEuclideanLin.symm φ.toLinearMap

/-- Conjugation by an isometry is conjugation by its matrix. -/
theorem conjIsometry_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (M : Op ι) :
    conjIsometry φ M = isometryMatrix φ * M * (isometryMatrix φ)ᴴ := rfl

/-- The matrix of an isometry acts on vectors as the isometry does. -/
theorem isometryMatrix_mulVec {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (x : EuclideanSpace ℂ ι) :
    isometryMatrix φ *ᵥ WithLp.ofLp x = WithLp.ofLp (φ x) := by
  have h : Matrix.toEuclideanLin (isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  have h' : Matrix.toEuclideanLin (isometryMatrix φ) x = φ x := by simp_all
  exact congrArg WithLp.ofLp h'

/-- The columns of the matrix of an isometry are the images of the basis
vectors. -/
theorem isometryMatrix_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (k : ι') (i : ι) :
    isometryMatrix φ k i =
      φ ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)) k := by
  rfl

/-- The matrix of a composite isometry is the product of the two matrices. -/
theorem isometryMatrix_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    isometryMatrix (φ.comp E) = isometryMatrix φ * isometryMatrix E := by
  ext k i
  rw [isometryMatrix_apply, Matrix.mul_apply]
  simp only [isometryMatrix_apply E]
  simpa [Matrix.mulVec, dotProduct] using (congrFun (isometryMatrix_mulVec φ
    (E ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)))) k).symm

/-- Conjugating by a composite isometry is conjugating twice.  This is how the
ground embeddings of the dilation combine with the local isometries produced by
the self-testing argument of blueprint
`thm:ms-rigidity`. -/
theorem conjIsometry_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) :
    conjIsometry (φ.comp E) M = conjIsometry φ (conjIsometry E M) := by
  simp [conjIsometry_eq, isometryMatrix_comp, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The two-sided isometry image of a bipartite state, written through the
Kronecker product of the two isometry matrices. -/
theorem isometryTensor_apply_eq {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : κA × κB) :
    isometryTensor φA φB ψ p =
      ∑ q : ιA × ιB,
        Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB) p q * ψ q := by
  simp [isometryTensor, Fintype.sum_prod_type, isometryMatrix_apply, EuclideanSpace.equiv, mul_assoc]

/-! ## Transfer of state-dependent bounds -/

/-- Conjugating an operator by the ground embedding inflates it: the result acts
as the original operator on the ground slice and annihilates the orthogonal
complement. -/
theorem conjIsometry_naimarkEmbedding {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : Op ι) :
    conjIsometry (naimarkEmbedding ι α) M = naimarkInflation (α := α) M := by
  ext p q
  rw [conjIsometry_eq]
  simp [Matrix.mul_apply, isometryMatrix_apply, naimarkEmbedding_apply, naimarkInflation_apply, EuclideanSpace.equiv]
  by_cases hp : p.2 = none
  · by_cases hq : q.2 = none <;> simp [hp, hq, eq_comm]
  · simp [hp]

/-- Conjugating an operator by the ground embedding followed by a later local
isometry is conjugating its inflation by that isometry.  This is the form in
which the conclusions of a self-testing argument applied to the dilated strategy
are read back on the original strategy. -/
theorem conjIsometry_comp_naimarkEmbedding {ι α κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) M =
      conjIsometry φ (naimarkInflation (α := α) M) := by
  rw [conjIsometry_comp, conjIsometry_naimarkEmbedding]

/-- Compressing one of Bob's dilated Magic Square effects to the ground slice
returns his original effect. -/
theorem naimarkCompression_msDilatedStrategy_B_effect (S : Strategy msGame)
    (y : MsType) (b : MsAnswer) :
    naimarkCompression (α := MsAnswer) (((msDilatedStrategy S).B y).effect b) =
      (S.B y).effect b := by
  ext i j
  exact dilatedMeasurement_compression _ _ _ _ _

/-- The action of an operator on the dilated state only sees its ground-slice
columns. -/
theorem applyOperatorToState_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (K : Op ((ιA × Option α) × (ιB × Option α)))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : (ιA × Option α) × (ιB × Option α)) :
    applyOperatorToState K (naimarkDilatedState α ψ) p =
      ∑ k : ιA, ∑ l : ιB, K p ((k, none), (l, none)) * ψ (k, l) := by
  classical
  simp [applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_option, naimarkDilatedState_apply]

/-- Inflated operators act on the dilated state exactly as the original
operators act on the original state.  This is the identity that transfers
state-dependent effect bounds back to the undilated strategy. -/
theorem applyOperatorToState_heteroKron_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (naimarkInflation (α := α) M) (naimarkInflation (α := α) N))
        (naimarkDilatedState α ψ) =
      naimarkDilatedState α (applyOperatorToState (heteroKron M N) ψ) := by
  classical
  ext p
  rw [applyOperatorToState_naimarkDilatedState, naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp [hob, heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_assoc]
    · simp [hob, heteroKron]
  · simp [hoa, heteroKron]

end

end MIPStarRE.QPBT.MagicSquareRigidity
