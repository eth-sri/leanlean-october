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

/-- The identity acts trivially. -/
theorem applyOperatorToState_one
    (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (1 : Op ι) v = v := by
  simp [applyOperatorToState]

/-- Operators act additively on states. -/
theorem applyOperatorToState_add
    (M : Op ι) (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u + v) =
      applyOperatorToState M u + applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- Operators act additively on differences of states. -/
theorem applyOperatorToState_sub
    (M : Op ι) (u v : EuclideanSpace ℂ ι) :
    applyOperatorToState M (u - v) =
      applyOperatorToState M u - applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- The action on states is additive in the operator. -/
theorem applyOperatorToState_add_op
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M + N) v =
      applyOperatorToState M v + applyOperatorToState N v := by
  simp [applyOperatorToState]

end

/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The squared norm of `A v` is the quadratic form of `Aᴴ A` at `v`. -/
theorem norm_toEuclideanLin_sq
    (A : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      (inner ℂ v (Matrix.toEuclideanLin (Aᴴ * A) v)).re := by
  rw [@norm_sq_eq_re_inner ℂ, Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A v)).re =
    (inner ℂ v ((Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A v))).re
  rw [LinearMap.adjoint_inner_right]

/-- A rectangular matrix `A` with `Aᴴ A = 1` preserves norms. -/
theorem norm_toEuclideanLin_of_conjTranspose_mul_eq_one {A : Matrix m n ℂ} (hA : Aᴴ * A = 1)
    (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A v‖ = ‖v‖ := by
  have h := norm_toEuclideanLin_sq A v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hone : Matrix.toEuclideanLin 1 v = v := by
    simp
  rw [hA, hone, hv] at h
  simp_all

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le
    {K : Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← DistanceCalculus.norm_applyOperatorToState_sq_eq, applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The difference of two contractions at most doubles norms. -/
theorem norm_applyOperatorToState_sub_le
    {A B : Op ι} (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - B) v‖ ≤ 2 * ‖v‖ := by
  have hsplit : applyOperatorToState (A - B) v =
      applyOperatorToState A v - applyOperatorToState B v := by
    simp [applyOperatorToState]
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  refine LE.le.trans_eq (add_le_add (norm_applyOperatorToState_le hA v)
  (norm_applyOperatorToState_le hB v)) ?_
  ring

/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj
    {P : Op ι} (hP : IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg

/-- Products of contractions are contractions. -/
theorem conjTranspose_mul_le_one_mul
    {A B : Op ι} (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    (A * B)ᴴ * (A * B) ≤ 1 := by
  have h1 := Matrix.le_iff.mp hA
  have h3 : Bᴴ * (1 - Aᴴ * A) * B = Bᴴ * B - (A * B)ᴴ * (A * B) := by
    simp
    noncomm_ring
  refine le_trans ?_ hB
  rw [Matrix.le_iff, ← h3]
  exact h1.conjTranspose_mul_mul_same B

end

/-- Effects of a measurement are contractions. -/
theorem conjTranspose_mul_le_one_of_effect {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (M.effect a)ᴴ * M.effect a ≤ 1 := by
  rw [measurement_effect_hermitian]
  exact le_trans (sq_le_self (M.pos a) (measurement_effect_le_one M a))
    (measurement_effect_le_one M a)

/-- The observable of a binary measurement is a contraction: writing
`E = M_0`, the observable is `2E - 1` and `1 - (2E - 1)² = 4(E - E²) ≥ 0`. -/
theorem conjTranspose_mul_le_one_of_obsOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    (obsOf M)ᴴ * obsOf M ≤ 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    rw [← M.sum_eq_one]
    exact (Fin.sum_univ_two _).symm
  have hobs : obsOf M = M.effect 0 + M.effect 0 - 1 := by
    simp [obsOf, ← hsum]
  rw [hobs]
  have hid : (M.effect 0 + M.effect 0 - 1)ᴴ * (M.effect 0 + M.effect 0 - 1) =
      1 - 4 • (M.effect 0 - M.effect 0 * M.effect 0) := by
    simp [(measurement_effect_hermitian M 0)]
    noncomm_ring
  rw [hid]
  exact sub_le_self _ (nsmul_nonneg (sub_nonneg.mpr (sq_le_self (M.pos 0) (measurement_effect_le_one M 0))) 4)

section

variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Left placement preserves contractions. -/
theorem conjTranspose_mul_le_one_leftTensor {A : Op ιA} (hA : Aᴴ * A ≤ 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A (1 : Op ιB) ≤ 1 := by
  change (leftTensor A)ᴴ * leftTensor A ≤ 1
  simp [leftTensor_mul_leftTensor]
  exact leftTensor_le_one hA

/-- Right placement preserves contractions. -/
theorem conjTranspose_mul_le_one_rightTensor {B : Op ιB} (hB : Bᴴ * B ≤ 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron (1 : Op ιA) B ≤ 1 := by
  change (rightTensor B)ᴴ * rightTensor B ≤ 1
  simp [rightTensor_mul_rightTensor]
  exact rightTensor_le_one hB

end

/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/

section

variable {β ιA ιB : Type*} (s : Finset β)

end

/-- The average over the one-point uniform distribution is the sum over the
outcomes. -/
theorem opFamilyDistSq_uniform_unit {γ ι : Type*} [Fintype γ] [Fintype ι]
    [DecidableEq ι] (M N : Unit → γ → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq (uniformDistribution Unit) M N ψ =
      ∑ c : γ, ‖applyOperatorToState (M () c - N () c) ψ‖ ^ 2 := by
  unfold opFamilyDistSq avgOver
  simp [uniformDistribution]

/-! ## Matrices of isometries -/

section

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')

/-- The matrix of an isometry is a matrix isometry. -/
theorem isometryMatrix_conjTranspose_mul :
    (isometryMatrix φ)ᴴ * isometryMatrix φ = 1 := by
  apply Matrix.toEuclideanLin.injective
  have hM : Matrix.toEuclideanLin (isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  calc
    _ =
        _ :=
      Matrix.toEuclideanLin_conjTranspose_mul_self _
    _ = φ.toLinearMap.adjoint.comp φ.toLinearMap := by rw [hM]
    _ = 1 := φ.adjoint_comp_self'
    _ = _ := by
      simp
      rfl

/-- The range projection `V Vᴴ` of a matrix isometry is at most the identity. -/
theorem isometryMatrix_mul_conjTranspose_le_one :
    isometryMatrix φ * (isometryMatrix φ)ᴴ ≤ 1 := by
  have hproj : IsProj (isometryMatrix φ * (isometryMatrix φ)ᴴ) := by
    constructor
    · change _ = isometryMatrix φ * (isometryMatrix φ)ᴴ
      simp [Matrix.mul_assoc, ← Matrix.mul_assoc (isometryMatrix φ)ᴴ, isometryMatrix_conjTranspose_mul]
    · change _ =
        isometryMatrix φ * (isometryMatrix φ)ᴴ
      simp [Matrix.star_eq_conjTranspose]
  exact sub_nonneg.mp hproj.one_sub.nonneg

/-- Conjugation by an isometry preserves contractions. -/
theorem conjTranspose_mul_le_one_conjIsometry {A : Op ι} (hA : Aᴴ * A ≤ 1) :
    (conjIsometry φ A)ᴴ * conjIsometry φ A ≤ 1 := by
  rw [conjIsometry_eq]
  have h1 : (isometryMatrix φ * A * (isometryMatrix φ)ᴴ)ᴴ *
      (isometryMatrix φ * A * (isometryMatrix φ)ᴴ) =
      isometryMatrix φ * (Aᴴ * A) * (isometryMatrix φ)ᴴ := by
    simp [Matrix.mul_assoc]
    simp [← Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  rw [h1]
  calc _ ≤
        isometryMatrix φ * (1 : Op ι) * (isometryMatrix φ)ᴴ := by
        rw [Matrix.le_iff]
        convert ((Matrix.le_iff.mp hA).mul_mul_conjTranspose_same (isometryMatrix φ)) using 1
        simp [Matrix.mul_sub, Matrix.sub_mul]
    _ = isometryMatrix φ * (isometryMatrix φ)ᴴ := by simp
    _ ≤ 1 := isometryMatrix_mul_conjTranspose_le_one φ

/-- Conjugation by an isometry is multiplicative. -/
theorem conjIsometry_mul (A B : Op ι) :
    conjIsometry φ A * conjIsometry φ B = conjIsometry φ (A * B) := by
  simp only [conjIsometry_eq, Matrix.mul_assoc]
  simp [← Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.one_mul]

/-- Conjugation by an isometry is additive. -/
theorem conjIsometry_sub (A B : Op ι) :
    conjIsometry φ (A - B) = conjIsometry φ A - conjIsometry φ B := by
  simp [conjIsometry_eq, Matrix.mul_sub, Matrix.sub_mul]

end

section

variable {ιA ιB κA κB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
  (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
  (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)

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

/-- The two-sided isometry image preserves norms. -/
theorem norm_isometryTensor
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖isometryTensor φA φB ψ‖ = ‖ψ‖ := by
  rw [isometryTensor_eq_toEuclideanLin]
  exact norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    ((by
       simp [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, isometryMatrix_conjTranspose_mul, Matrix.one_kronecker_one])) ψ

/-- A left-placed conjugated operator acts on the transported state as the
left-placed original operator acts on the original state. -/
theorem applyOperatorToState_leftTensor_conjIsometry
    (X : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron (conjIsometry φA X) 1) (isometryTensor φA φB ψ) =
      isometryTensor φA φB (applyOperatorToState (heteroKron X 1) ψ) := by
  simp [isometryTensor_eq_toEuclideanLin, applyOperatorToState, heteroKron, Matrix.kronecker, ← toEuclideanLin_mul_apply, conjIsometry_eq, ← Matrix.mul_kronecker_mul, Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul]

/-- A right-placed conjugated operator acts on the transported state as the
right-placed original operator acts on the original state. -/
theorem applyOperatorToState_rightTensor_conjIsometry
    (Y : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron 1 (conjIsometry φB Y)) (isometryTensor φA φB ψ) =
      isometryTensor φA φB (applyOperatorToState (heteroKron 1 Y) ψ) := by
  simp [isometryTensor_eq_toEuclideanLin, applyOperatorToState, heteroKron, Matrix.kronecker, ← toEuclideanLin_mul_apply, conjIsometry_eq, ← Matrix.mul_kronecker_mul, Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul]

end

/-! ## The ground projection -/

/-- The orthogonal projection of an enlarged local space onto its ground slice,
namely the inflation of the identity.  Formalization-only support for the
transfer step of blueprint `thm:ms-rigidity`. -/
def groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Op (ι × Option α) :=
  naimarkInflation (α := α) (1 : Op ι)

section

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul (M N : Op ι) :
    naimarkInflation (α := α) M * naimarkInflation (α := α) N =
      naimarkInflation (α := α) (M * N) := by
  ext p q
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Inflation commutes with the conjugate transpose. -/
theorem naimarkInflation_conjTranspose (M : Op ι) :
    (naimarkInflation (α := α) M)ᴴ = naimarkInflation (α := α) Mᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, naimarkInflation_apply]
  grind

end

/-- The ground projection is an orthogonal projection. -/
theorem isProj_groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : IsProj (groundProjection ι α) := by
  constructor
  · change _ = groundProjection ι α
    simp [groundProjection, naimarkInflation_mul]
  · change _ = groundProjection ι α
    simp [Matrix.star_eq_conjTranspose, groundProjection, naimarkInflation_conjTranspose]

/-- Inflating the compression of an operator to the ground slice is compressing
it by the ground projection. -/
theorem naimarkInflation_naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : Op (ι × Option α)) :
    naimarkInflation (α := α) (naimarkCompression (α := α) P) =
      groundProjection ι α * P * groundProjection ι α := by
  ext p q
  simp [Matrix.mul_apply, naimarkCompression_apply, groundProjection, Fintype.sum_prod_type, Fintype.sum_option, Matrix.one_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_finset_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (s : Finset β) (M : β → Op (ι × Option α)) :
    naimarkCompression (α := α) (∑ b ∈ s, M b) =
      ∑ b ∈ s, naimarkCompression (α := α) (M b) := by
  ext i j
  simp [Matrix.sum_apply]

variable (α : Type) [Fintype α] [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
  [Fintype ιB] [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- The dilated state lies in the ground slice on Alice's side. -/
theorem applyOperatorToState_leftTensor_groundProjection :
    applyOperatorToState (heteroKron (groundProjection ιA α) 1) (naimarkDilatedState α ψ) =
      naimarkDilatedState α ψ := by
  have hfull : applyOperatorToState
      (heteroKron (groundProjection ιA α) (groundProjection ιB α))
      (naimarkDilatedState α ψ) = naimarkDilatedState α ψ := by
    simp [groundProjection, applyOperatorToState_heteroKron_naimarkInflation, heteroKron_one_one, applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  simp [← applyOperatorToState_mul, heteroKron_mul, (isProj_groundProjection ιA α).isIdempotentElem.eq]
  exact hfull

/-- The dilated state lies in the ground slice on Bob's side. -/
theorem applyOperatorToState_rightTensor_groundProjection :
    applyOperatorToState (heteroKron 1 (groundProjection ιB α)) (naimarkDilatedState α ψ) =
      naimarkDilatedState α ψ := by
  have hfull : applyOperatorToState
      (heteroKron (groundProjection ιA α) (groundProjection ιB α))
      (naimarkDilatedState α ψ) = naimarkDilatedState α ψ := by
    simp [groundProjection, applyOperatorToState_heteroKron_naimarkInflation, heteroKron_one_one, applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  simp [← applyOperatorToState_mul, heteroKron_mul, (isProj_groundProjection ιB α).isIdempotentElem.eq]
  exact hfull

/-- The complement of the ground slice annihilates the dilated state on Bob's
side. -/
theorem applyOperatorToState_rightTensor_one_sub_groundProjection :
    applyOperatorToState (heteroKron 1 (1 - groundProjection ιB α))
      (naimarkDilatedState α ψ) = 0 := by
  have hsub : applyOperatorToState (1 - heteroKron 1 (groundProjection ιB α))
      (naimarkDilatedState α ψ) =
      applyOperatorToState 1 (naimarkDilatedState α ψ) -
        applyOperatorToState (heteroKron 1 (groundProjection ιB α))
          (naimarkDilatedState α ψ) := by
    simp [applyOperatorToState]
  simp [heteroKron_sub_right, heteroKron_one_one, hsub, applyOperatorToState_one, applyOperatorToState_rightTensor_groundProjection]

/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/

section

variable (P : Op (ιA × Option α)) (Q : Op (ιB × Option α))

/-- The leakage of a right-placed operator `Q` out of the ground slice on the
dilated state is at most its intertwining defect against any left-placed
operator. -/
theorem norm_rightTensor_one_sub_groundProjection_mul_le :
    ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * Q))
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron P 1 - heteroKron 1 Q)
        (naimarkDilatedState α ψ)‖ := by
  set ψ' := naimarkDilatedState α ψ
  set L : Op ((ιA × Option α) × (ιB × Option α)) :=
    heteroKron 1 (1 - groundProjection ιB α)
  have hLcontr : Lᴴ * L ≤ 1 :=
    conjTranspose_mul_le_one_rightTensor
      (conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιB α).one_sub)
  have hsplit : heteroKron 1
      ((1 - groundProjection ιB α) * Q) = L * heteroKron 1 Q := by
    rw [heteroKron_mul, Matrix.one_mul]
  have hcomm : L * heteroKron P 1 = heteroKron P 1 * L := by
    rw [heteroKron_mul, heteroKron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have key : applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * Q)) ψ' =
      applyOperatorToState L
        (applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ') := by
    rw [hsplit, applyOperatorToState_mul]
    have hdec : applyOperatorToState (heteroKron 1 Q) ψ' =
        applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ' +
          applyOperatorToState (heteroKron P 1) ψ' := by
      simp [applyOperatorToState]
    rw [hdec, applyOperatorToState_add, ← applyOperatorToState_mul L (heteroKron P 1), hcomm,
      applyOperatorToState_mul, (applyOperatorToState_rightTensor_one_sub_groundProjection α ψ), (show applyOperatorToState _ (0 : EuclideanSpace ℂ _) = 0 by simp [applyOperatorToState]), add_zero]
  have hneg : -applyOperatorToState (heteroKron P 1 - heteroKron 1 Q) ψ' =
      applyOperatorToState (heteroKron 1 Q - heteroKron P 1) ψ' := by
    simp [applyOperatorToState]
  rw [key]
  refine LE.le.trans_eq (norm_applyOperatorToState_le hLcontr _) ?_
  simp [← hneg]

end

end

end MIPStarRE.QPBT.MagicSquareRigidity
