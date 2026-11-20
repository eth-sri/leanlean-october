module

public import QPBT.Games.DistanceTheorems
public import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation

/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
include ι

section

variable (M : Op ι)
include M

/-- Operators act additively on states. -/
theorem applyOperatorToState_add (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u + v) =
      applyOperatorToState M u + applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- Operators act additively on differences of states. -/
theorem applyOperatorToState_sub (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u - v) =
      applyOperatorToState M u - applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op (N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M - N) v =
      applyOperatorToState M v - applyOperatorToState N v := by
  simp [applyOperatorToState]

/-- The action on states is additive in the operator. -/
theorem applyOperatorToState_add_op (N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M + N) v =
      applyOperatorToState M v + applyOperatorToState N v := by
  simp [applyOperatorToState]

/-- Operators annihilate the zero state. -/
theorem applyOperatorToState_zero :
    applyOperatorToState M (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [applyOperatorToState]

end

end

/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by simp

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
include m n

/-- The squared norm of `A v` is the quadratic form of `Aᴴ A` at `v`. -/
theorem norm_toEuclideanLin_sq
    (A : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      (inner ℂ v (Matrix.toEuclideanLin (Aᴴ * A) v)).re := by simp_all [@norm_sq_eq_re_inner ℂ, Matrix.toEuclideanLin_conjTranspose_mul_self, LinearMap.adjoint_inner_right]

/-- A rectangular matrix `A` with `Aᴴ A = 1` preserves norms. -/
theorem norm_toEuclideanLin_of_conjTranspose_mul_eq_one {A : Matrix m n ℂ} (hA : Aᴴ * A = 1)
    (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ = ‖v‖ := by
  have h := norm_toEuclideanLin_sq A v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  simp_all

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le
    {K : Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState K v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_applyOperatorToState_sq, ← stateQForm_one]
  exact stateQForm_mono v hK

/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj
    {P : Op ι} (hP : IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg

/-- Effects of a measurement are contractions. -/
theorem conjTranspose_mul_le_one_of_effect {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (M.effect a)ᴴ * M.effect a ≤ 1 := by
  rw [measurement_effect_hermitian]
  exact le_trans (sq_le_self (M.pos a) (measurement_effect_le_one M a))
    (measurement_effect_le_one M a)

/-- The observable of a binary measurement is a contraction: writing
`E = M_0`, the observable is `2E - 1` and `1 - (2E - 1)² = 4(E - E²) ≥ 0`. -/
theorem conjTranspose_mul_le_one_of_obsOf
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    (obsOf M)ᴴ * obsOf M ≤ 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    calc
      M.effect 0 + M.effect 1 = ∑ a : ZMod 2, M.effect a :=
        (Fin.sum_univ_two _).symm
      _ = 1 := M.sum_eq_one
  have hobs : obsOf M = M.effect 0 + M.effect 0 - 1 := by
    unfold obsOf
    rw [← hsum]
    abel
  have hH := measurement_effect_hermitian M 0
  have hsq :=
    sub_nonneg.mpr (sq_le_self (M.pos 0) (measurement_effect_le_one M 0))
  rw [hobs]
  have hid : (M.effect 0 + M.effect 0 - 1)ᴴ * (M.effect 0 + M.effect 0 - 1) =
      1 - (4 : ℕ) • (M.effect 0 - M.effect 0 * M.effect 0) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, hH]
    noncomm_ring
  rw [hid]
  exact sub_le_self _ (nsmul_nonneg hsq 4)

end

/-- Left placement preserves contractions. -/
theorem conjTranspose_mul_le_one_leftTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {A : Op ιA} (hA : Aᴴ * A ≤ 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A (1 : Op ιB) ≤ 1 := by
  change (leftTensor (ι₂ := ιB) A)ᴴ * leftTensor (ι₂ := ιB) A ≤ 1
  rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
  exact leftTensor_le_one hA

/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/

/-- The average over the one-point uniform distribution is the sum over the
outcomes. -/
theorem opFamilyDistSq_uniform_unit {γ ι : Type*} [Fintype γ] [Fintype ι]
    [DecidableEq ι] (M N : Unit → γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq (uniformDistribution Unit) M N ψ =
      ∑ c : γ, ‖applyOperatorToState (M () c - N () c) ψ‖ ^ 2 := by
  unfold opFamilyDistSq avgOver
  simp [uniformDistribution]

/-! ## Matrices of isometries -/

/-- The matrix of an isometry is a matrix isometry. -/
theorem isometryMatrix_conjTranspose_mul {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    (isometryMatrix φ)ᴴ * isometryMatrix φ = 1 := by
  apply Matrix.toEuclideanLin.injective
  have hM : Matrix.toEuclideanLin (isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  calc
    Matrix.toEuclideanLin ((isometryMatrix φ)ᴴ * isometryMatrix φ) =
        (Matrix.toEuclideanLin (isometryMatrix φ)).adjoint.comp
          (Matrix.toEuclideanLin (isometryMatrix φ)) :=
      Matrix.toEuclideanLin_conjTranspose_mul_self _
    _ = φ.toLinearMap.adjoint.comp φ.toLinearMap := by rw [hM]
    _ = 1 := φ.adjoint_comp_self'
    _ = Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) := by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
      rfl

/-- Conjugation by an isometry is multiplicative. -/
theorem conjIsometry_mul {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (A B : Op ι) :
    conjIsometry φ A * conjIsometry φ B = conjIsometry φ (A * B) := by
  simp [conjIsometry_eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (isometryMatrix φ)ᴴ (isometryMatrix φ),
    isometryMatrix_conjTranspose_mul, Matrix.one_mul]


section

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
include ι κ φ

/-- Conjugation by an isometry preserves the adjoint. -/
theorem conjIsometry_conjTranspose (A : Op ι) :
    (conjIsometry φ A)ᴴ = conjIsometry φ (Aᴴ) := by
  simp [conjIsometry_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Orthogonal projections are preserved by isometry conjugation. -/
theorem isProj_conjIsometry {A : Op ι} (h : IsProj A) :
    IsProj (conjIsometry φ A) := by
  refine ⟨?_, ?_⟩
  · change conjIsometry φ A * conjIsometry φ A = _
    rw [conjIsometry_mul, h.isIdempotentElem.eq]
  · simp only [IsSelfAdjoint, Matrix.star_eq_conjTranspose, conjIsometry_conjTranspose,
      h.isSelfAdjoint.isHermitian.eq]

/-- Conjugation sends the identity to the range projection. -/
theorem isProj_conjIsometry_one :
    IsProj (conjIsometry φ 1) :=
  isProj_conjIsometry φ ⟨by simp [IsIdempotentElem], by simp [IsSelfAdjoint]⟩

/-- The range projection of an isometry is at most the identity. -/
theorem conjIsometry_one_le_one :
    conjIsometry φ 1 ≤ 1 :=
  sub_nonneg.mp (isProj_conjIsometry_one φ).one_sub.nonneg

/-- Conjugation by an isometry is monotone. -/
theorem conjIsometry_mono {A B : Op ι} (h : A ≤ B) :
    conjIsometry φ A ≤ conjIsometry φ B := by
  rw [conjIsometry_eq, conjIsometry_eq, Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (Matrix.le_iff.mp h).mul_mul_conjTranspose_same (isometryMatrix φ)

/-- Conjugation by an isometry preserves contractions. -/
theorem conjTranspose_mul_le_one_conjIsometry {A : Op ι} (hA : Aᴴ * A ≤ 1) :
    (conjIsometry φ A)ᴴ * conjIsometry φ A ≤ 1 := by
  rw [conjIsometry_conjTranspose, conjIsometry_mul]
  exact (conjIsometry_mono φ hA).trans (conjIsometry_one_le_one φ)

end

/-- Conjugation by an isometry preserves square-summability. -/
theorem conjIsometry_sum_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) {N : α → Op ι}
    (h : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) ≤ 1 := by
  simp_rw [conjIsometry_conjTranspose, conjIsometry_mul, conjIsometry_eq,
    ← Matrix.sum_mul, ← Matrix.mul_sum]
  exact (conjIsometry_mono φ h).trans (conjIsometry_one_le_one φ)

section

variable {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
include ιA ιB κA κB φA φB

/-- The two-sided isometry image of a state is the action of the Kronecker
product of the two isometry matrices. -/
theorem isometryTensor_eq_toEuclideanLin
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor φA φB ψ =
      Matrix.toEuclideanLin
        (Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB)) ψ := by
  ext p
  rw [isometryTensor_apply_eq]
  rfl

/-- The Kronecker product of two matrix isometries is a matrix isometry. -/
theorem kronecker_isometryMatrix_conjTranspose_mul :
    (Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB))ᴴ *
      Matrix.kronecker (isometryMatrix φA) (isometryMatrix φB) = 1 := by
  unfold Matrix.kronecker
  simp_all [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, isometryMatrix_conjTranspose_mul, Matrix.one_kronecker_one]

/-- The two-sided isometry image preserves norms. -/
theorem norm_isometryTensor
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖isometryTensor φA φB ψ‖ = ‖ψ‖ := by
  rw [isometryTensor_eq_toEuclideanLin]
  exact norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    (kronecker_isometryMatrix_conjTranspose_mul φA φB) ψ

/-- A left-placed conjugated operator acts on the transported state as the
left-placed original operator acts on the original state. -/
theorem applyOperatorToState_leftTensor_conjIsometry
    (X : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (conjIsometry φA X) 1) (isometryTensor φA φB ψ) =
      isometryTensor φA φB (applyOperatorToState (heteroKron X 1) ψ) := by
  rw [isometryTensor_eq_toEuclideanLin, isometryTensor_eq_toEuclideanLin]
  unfold applyOperatorToState
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply]
  refine congrArg (fun M => Matrix.toEuclideanLin M ψ) ?_
  unfold heteroKron Matrix.kronecker
  rw [conjIsometry_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

end

/-! ## The ground projection -/

/-- The orthogonal projection of an enlarged local space onto its ground slice,
namely the inflation of the identity.  Formalization-only support for the
transfer step of blueprint `thm:ms-rigidity`. -/
def groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Op (ι × Option α) :=
  naimarkInflation (α := α) (1 : Op ι)

section

variable {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]

/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul (M N : Op ι) :
    naimarkInflation (α := α) M * naimarkInflation (α := α) N =
      naimarkInflation (α := α) (M * N) := by
  ext p q
  simp only [Matrix.mul_apply, naimarkInflation_apply, Fintype.sum_prod_type,
    Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp_all

/-- Inflation commutes with the conjugate transpose. -/
theorem naimarkInflation_conjTranspose (M : Op ι) :
    (naimarkInflation (α := α) M)ᴴ = naimarkInflation (α := α) Mᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, naimarkInflation_apply]
  grind

/-- The ground projection is an orthogonal projection. -/
theorem isProj_groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : IsProj (groundProjection ι α) := by
  constructor
  · change groundProjection ι α * groundProjection ι α = groundProjection ι α
    rw [groundProjection, naimarkInflation_mul, Matrix.mul_one]
  · change star (groundProjection ι α) = groundProjection ι α
    rw [Matrix.star_eq_conjTranspose, groundProjection, naimarkInflation_conjTranspose,
      Matrix.conjTranspose_one]

/-- Inflating the compression of an operator to the ground slice is compressing
it by the ground projection. -/
theorem naimarkInflation_naimarkCompression (P : Op (ι × Option α)) :
    naimarkInflation (α := α) (naimarkCompression (α := α) P) =
      groundProjection ι α * P * groundProjection ι α := by
  ext p q
  simp only [Matrix.mul_apply, naimarkInflation_apply, naimarkCompression_apply,
    groundProjection, Fintype.sum_prod_type, Fintype.sum_option, Matrix.one_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp_all

end

/-- Compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_finset_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (s : Finset β) (M : β → Op (ι × Option α)) :
    naimarkCompression (α := α) (∑ b ∈ s, M b) =
      ∑ b ∈ s, naimarkCompression (α := α) (M b) := by
  ext i j
  simp [Matrix.sum_apply]

section

variable (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
include α ιA ιB ψ

/-- The dilated state lies in the ground slice on Alice's side. -/
theorem applyOperatorToState_leftTensor_groundProjection :
    applyOperatorToState (heteroKron (groundProjection ιA α) 1) (naimarkDilatedState α ψ) =
      naimarkDilatedState α ψ := by
  have hfull : applyOperatorToState
      (heteroKron (groundProjection ιA α) (groundProjection ιB α))
      (naimarkDilatedState α ψ) = naimarkDilatedState α ψ := by
    rw [groundProjection, groundProjection, applyOperatorToState_heteroKron_naimarkInflation,
      heteroKron_one_one, applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  rw [← applyOperatorToState_mul, heteroKron_mul,
    (isProj_groundProjection ιA α).isIdempotentElem.eq, Matrix.one_mul]
  assumption

/-- The complement of the ground slice annihilates the dilated state on Alice's
side. -/
theorem applyOperatorToState_leftTensor_one_sub_groundProjection :
    applyOperatorToState (heteroKron (1 - groundProjection ιA α) 1)
      (naimarkDilatedState α ψ) = 0 := by
  rw [heteroKron_sub_left, heteroKron_one_one, applyOperatorToState_sub_op,
    applyOperatorToState_one, applyOperatorToState_leftTensor_groundProjection, sub_self]

end

/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/

/-- The leakage of a left-placed operator `P` out of the ground slice on the
dilated state is at most the intertwining defect of `P ⊗ 1` against any
right-placed operator `1 ⊗ Q`, because `(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.
This is the estimate replacing the `≈_δ` preservation that Naimark dilation
lacks (`references/ldt-paper/orthonormalization.tex:82-101`). -/
theorem norm_leftTensor_one_sub_groundProjection_mul_le (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (P : Op (ιA × Option α)) (Q : Op (ιB × Option α)) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * P) 1)
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron P 1 - heteroKron 1 Q)
        (naimarkDilatedState α ψ)‖ := by
  set ψ' := naimarkDilatedState α ψ
  set L : Op ((ιA × Option α) × (ιB × Option α)) :=
    heteroKron (1 - groundProjection ιA α) 1
  have hL0 : applyOperatorToState L ψ' = 0 :=
    applyOperatorToState_leftTensor_one_sub_groundProjection α ψ
  have hLcontr : Lᴴ * L ≤ 1 :=
    conjTranspose_mul_le_one_leftTensor
      (conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιA α).one_sub)
  have hz : applyOperatorToState (L * heteroKron 1 Q) ψ' = 0 := by
    rw [show L * heteroKron 1 Q = heteroKron 1 Q * L by
      simp only [L, heteroKron_mul, Matrix.one_mul, Matrix.mul_one],
      applyOperatorToState_mul, hL0, applyOperatorToState_zero]
  have h := norm_applyOperatorToState_le hLcontr
    (applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ')
  rw [← applyOperatorToState_mul, mul_sub, applyOperatorToState_sub_op, hz, sub_zero] at h
  simpa only [L, heteroKron_mul, Matrix.one_mul] using h


end

end MIPStarRE.QPBT.MagicSquareRigidity
