module

public import QPBT.Games.DistanceTheorems.Support

/-! Tensor products of states and their operator expectations. -/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

section

variable {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
include ι κ

/-- A Kronecker product of operators acts factorwise on a coordinate tensor.
Formalization-only support for `def:expanded-state`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem applyOperatorToState_heteroKron_vecTensor
    (A : Op ι) (B : Op κ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    applyOperatorToState (heteroKron A B) (vecTensor u v) =
      vecTensor (applyOperatorToState A u) (applyOperatorToState B v) := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  change (Matrix.mulVec (heteroKron A B) (vecTensor u v).ofLp) (i, j) =
    (Matrix.mulVec A u.ofLp) i * (Matrix.mulVec B v.ofLp) j
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec,
    Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  change heteroKron A B (i, j) (k, l) * (vecTensor u v).ofLp (k, l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  change A i k * B j l * (u.ofLp k * v.ofLp l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  ring

/-- The inner product of coordinate tensors is the product of the factor
inner products. Formalization-only support for the EPR product calculation in
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem inner_vecTensor (u x : EuclideanSpace ℂ ι) (v y : EuclideanSpace ℂ κ) :
    inner ℂ (vecTensor u v) (vecTensor x y) = inner ℂ u x * inner ℂ v y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ p : ι × κ,
      (x.ofLp p.1 * y.ofLp p.2) * star (u.ofLp p.1 * v.ofLp p.2)) =
    (∑ i : ι, x.ofLp i * star (u.ofLp i)) *
      ∑ j : κ, y.ofLp j * star (v.ofLp j)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul]
  ring

end

/-- Evaluating a tensor product on a product state factors when the right
operator has real expectation. -/
theorem stateQForm_vecTensor_right_hermitian {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Op I) (B : Op J) (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J)
    (hB : B.IsHermitian) :
    stateQForm (vecTensor u v) (heteroKron A B) = stateQForm u A * stateQForm v B := by
  have him : (inner ℂ v (applyOperatorToState B v)).im = 0 :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).im_inner_self_apply v
  unfold stateQForm
  rw [applyOperatorToState_heteroKron_vecTensor, inner_vecTensor, Complex.mul_re, him, mul_zero, sub_zero]

/-- Kronecker products preserve Hermiticity. -/
theorem heteroKron_isHermitian {I J : Type*} {A : Op I} {B : Op J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (heteroKron A B).IsHermitian := by
  rw [Matrix.IsHermitian, heteroKron_conjTranspose, hA.eq, hB.eq]

/-- Unshuffling players' coordinates separates the strategy and ancillary operators. -/
theorem reindexOp_prodShuffle_heteroKron {I J K L : Type*}
    (A : Op I) (B : Op J) (R : Op K) (T : Op L) :
    reindexOp prodShuffle (heteroKron (heteroKron A R) (heteroKron B T)) =
      heteroKron (heteroKron A B) (heteroKron R T) := by
  ext p q
  change (A p.1.1 q.1.1 * R p.2.1 q.2.1) * (B p.1.2 q.1.2 * T p.2.2 q.2.2) = _
  change _ = (A p.1.1 q.1.1 * B p.1.2 q.1.2) * (R p.2.1 q.2.1 * T p.2.2 q.2.2)
  ring

end MIPStarRE.QPBT
