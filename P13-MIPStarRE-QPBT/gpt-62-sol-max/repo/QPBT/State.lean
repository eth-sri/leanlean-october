module

public import QPBT.Upstream

public import MIPStarRE.Quantum.FiniteMatrix.Basic

/-!
# Finite-dimensional state transformations

This file defines the tensor and reindexing operations used for strategy
distance, Magic Square rigidity, and the qudit-to-qubit isomorphism. See
blueprint chapters 11--13 and the declaration-level references below.
-/

@[expose] public section

open scoped Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

/-- Conjugation by the local isometries in `thm:ms-rigidity` and
`lem:pauli-binary`; blueprint `thm:ms-rigidity` and
`lem:pauli-binary`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652` and
`04_preliminaries.tex:1163-1208`. -/
noncomputable def conjIsometry {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι')
    (M : Op ι) : Op ι' :=
  let U : Matrix ι' ι ℂ := Matrix.toEuclideanLin.symm φ.toLinearMap
  U * M * Uᴴ

/-- Coordinate transport used by blueprint
`def:strategy-distance`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
noncomputable def reindexState {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι' :=
  (EuclideanSpace.equiv ι' ℂ).symm
    (fun j => (EuclideanSpace.equiv ι ℂ ψ) (e.symm j))

/-- Apply the two independent local isometries of blueprint
`thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
noncomputable def isometryTensor
    {ιA ιB κA κB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ (κA × κB) :=
  (EuclideanSpace.equiv (κA × κB) ℂ).symm
    (fun p =>
      ∑ i : ιA, ∑ j : ιB,
        ((EuclideanSpace.equiv κA ℂ)
            (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1) *
          ((EuclideanSpace.equiv κB ℂ)
            (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2) *
          ((EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)))

/-- Interchanging the factors commutes with applying the two local isometries. -/
theorem isometryTensor_prodComm {ιA ιB κA κB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor φB φA (reindexState (Equiv.prodComm ιA ιB) ψ) =
      reindexState (Equiv.prodComm κA κB) (isometryTensor φA φB ψ) := by
  apply (EuclideanSpace.equiv (κB × κA) ℂ).injective
  simp only [isometryTensor, reindexState, ContinuousLinearEquiv.apply_symm_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply]
  funext p
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- Coordinate tensor used in the ideal state of blueprint
`thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
noncomputable def vecTensor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm
    (fun p => (EuclideanSpace.equiv ι ℂ u) p.1 * (EuclideanSpace.equiv κ ℂ v) p.2)

/-- Operator transport used by blueprint
`def:strategy-distance`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
def reindexOp {ι ι' : Type*} (e : ι ≃ ι') (M : Op ι') : Op ι :=
  (Matrix.reindex e.symm e.symm) M

/-- Operator transport commutes with subtraction. -/
theorem reindexOp_sub {ι κ : Type*} (e : ι ≃ κ) (M N : Op κ) :
    reindexOp e (M - N) = reindexOp e M - reindexOp e N := rfl

/-- Operator transport commutes with scalar multiplication. -/
theorem reindexOp_smul {ι κ : Type*} (e : ι ≃ κ) (c : ℂ) (M : Op κ) :
    reindexOp e (c • M) = c • reindexOp e M := rfl

/-- Operator transport commutes with multiplication. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M N : Op κ) :
    reindexOp e (M * N) = reindexOp e M * reindexOp e N :=
  map_mul (Matrix.reindexRingEquiv ℂ e.symm) M N

/-- Relabeling an operator distributes over summation. -/
theorem reindexOp_sum {ι κ α : Type*} (e : ι ≃ κ) (s : Finset α) (A : α → Op κ) :
    reindexOp e (∑ a ∈ s, A a) = ∑ a ∈ s, reindexOp e (A a) := by
  ext i j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.sum_apply]

/-- An identity operator is independent of its coordinate names. -/
theorem reindexOp_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    reindexOp e (1 : Op κ) = 1 := by
  ext i j
  simp [reindexOp, Matrix.one_apply]

/-- Forward relabeling also fixes the identity. -/
theorem matrixReindex_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix.reindex e e (1 : Op ι) = 1 := reindexOp_one e.symm

/-- Separate relabeling of two factors commutes with their tensor product. -/
theorem reindex_kronecker {I J K L : Type*} (e : I ≃ K) (f : J ≃ L)
    (A : Op I) (B : Op J) :
    Matrix.reindex (e.prodCongr f) (e.prodCongr f) (Matrix.kronecker A B) =
      Matrix.kronecker (Matrix.reindex e e A) (Matrix.reindex f f B) := rfl

/-- Four-factor tensor shuffle used by blueprint
`thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:620-652`. -/
def prodShuffle {α β γ δ : Type*} :
    (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv p := by rfl
  right_inv p := by rfl

/-! ## Norm identities for the coordinate operations -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reindexing is Mathlib's Euclidean permutation isometry. -/
theorem reindexState_eq (e : ι ≃ κ) (ψ : EuclideanSpace ℂ ι) :
    reindexState e ψ = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e ψ := rfl

/-- Reindexing Euclidean coordinates preserves the norm. -/
theorem reindexState_norm_eq (e : ι ≃ κ) (ψ : EuclideanSpace ℂ ι) :
    ‖reindexState e ψ‖ = ‖ψ‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map ψ

/-- Reindexing preserves the distance between Euclidean vectors. -/
theorem norm_reindexState_sub_eq (e : ι ≃ κ) (ψ φ : EuclideanSpace ℂ ι) :
    ‖reindexState e ψ - reindexState e φ‖ = ‖ψ - φ‖ :=
  reindexState_norm_eq e (ψ - φ)

/-- The coordinate tensor of two Euclidean vectors has the product norm.
This is a formalization-only auxiliary identity (no source counterpart). -/
theorem vecTensor_norm_eq
    {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (u : EuclideanSpace ℂ iota) (v : EuclideanSpace ℂ kappa) :
    ‖vecTensor u v‖ = ‖u‖ * ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  change (∑ p : iota × kappa, ‖u p.1 * v p.2‖ ^ 2) =
    (∑ i : iota, ‖u i‖ ^ 2) * ∑ j : kappa, ‖v j‖ ^ 2
  simp [norm_mul, mul_pow]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

end MIPStarRE.QPBT
