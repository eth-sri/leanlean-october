module

public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Range projections in Pauli soundness

Inserting an orthogonal projection into a measurement comparison costs at most
twice the squared distance to a vector fixed by that projection. Summing over
the measurement outcomes introduces no factor depending on their number.

## References

These are formalization-only auxiliary estimates for the final proof of
blueprint `thm:pauli`. The range projection is omitted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`;
the corrected calculation is given in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
They do not construct the extraction data or prove Pauli soundness.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open DistanceCalculus MagicSquareRigidity

variable {α ι ιA κ ιB κA κB : Type} [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [Fintype ιA] (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
  [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype κA] [DecidableEq κA] [Fintype κB]
  [DecidableEq κB] (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
  (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)

/-- The identity conjugated by an isometry is its orthogonal range projection. -/
private theorem conjIsometry_one_isProj :
    IsProj (conjIsometry phi 1) := by
  constructor
  · change _ = conjIsometry phi 1
    simp [conjIsometry_mul]
  · change _ = conjIsometry phi 1
    simp [conjIsometry_eq, Matrix.star_eq_conjTranspose]

/-- Intertwining identifies isometry conjugation with insertion of its range projection. -/
private theorem mul_conjIsometry_one_eq {M : Op ι} {N : Op κ}
    (hintertwine : N * isometryMatrix phi = isometryMatrix phi * M) :
    N * conjIsometry phi 1 = conjIsometry phi M := by
  rw [conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hintertwine]
  rfl

/-- Inserting a projection that fixes `theta` into a complete POVM costs at most
twice the squared distance from the comparison state to `theta`, in addition
to twice the original operator-family distance. This is blueprint
`thm:pauli-range-projection-support`, the analytic range-projection estimate
supporting `thm:pauli`. It holds for every complete POVM. -/
theorem sum_norm_mul_projection_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N : MIPStarRE.Quantum.Measurement α ι) (T : α → Op ι)
    (Q : Op ι) (hQ : IsProj Q) (theta delta : EuclideanSpace ℂ ι)
    (htheta : applyOperatorToState Q theta = theta) :
    ∑ a : α, ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * ‖delta - theta‖ ^ 2 := by
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    have hfix : Matrix.toEuclideanLin Q theta = theta := htheta
    simp [applyOperatorToState, hfix]
  calc
    _ ≤
        ∑ a : α, (2 * ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2 +
          2 * ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      have hsplit : N.effect a * Q - T a =
          (N.effect a - T a) - N.effect a * (1 - Q) := by
        rw [mul_sub, mul_one]
        abel
      rw [hsplit, applyOperatorToState, map_sub, LinearMap.sub_apply]
      exact (le_add_of_nonneg_left (sq_nonneg
        ‖applyOperatorToState (N.effect a - T a) delta +
          applyOperatorToState (N.effect a * (1 - Q)) delta‖)).trans_eq
        ((parallelogram_law_with_norm ℂ
          (applyOperatorToState (N.effect a - T a) delta)
          (applyOperatorToState (N.effect a * (1 - Q)) delta)).trans (mul_add 2 _ _))
    _ = 2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * (∑ a : α, ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((sum_norm_mul_apply_le N.effect (1 - Q) delta
        (MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one N)).trans (by
        have hnorm := norm_applyOperatorToState_le
          (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
        simp [applyOperatorToState_sub, hvanish] at hnorm
        gcongr)) (by norm_num))

/-- Alice's isometry transfer on a bipartite comparison state. The state error
uses both local isometries, while each effect is conjugated only by Alice's
isometry, as required by blueprint `thm:pauli`. The exact local intertwining
identity is the one obtained from the ancilla extension and swap unitary.
This is blueprint `thm:pauli-isometry-transfer-alice-support`. -/
theorem sum_norm_leftTensor_conjIsometry_sub_sq_le
    (M : α → Op ιA) (N : MIPStarRE.Quantum.Measurement α κA)
    (T : α → Op (κA × κB))
    (hintertwine : ∀ a : α,
      N.effect a * isometryMatrix phiA = isometryMatrix phiA * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a : α, ‖applyOperatorToState
        (heteroKron (conjIsometry phiA (M a)) 1 - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (heteroKron (N.effect a) 1 - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron (conjIsometry phiA 1) 1
  have hcompression (a : α) : (leftPlacedMeasurement N).effect a * Q =
      heteroKron (conjIsometry phiA (M a)) 1 := by
    change heteroKron (N.effect a) 1 * heteroKron _ 1 = _
    simp [heteroKron_mul, mul_conjIsometry_one_eq phiA (hintertwine a)]
  have hbound := sum_norm_mul_projection_sub_sq_le (leftPlacedMeasurement N) T Q (by
    constructor
    · change Q * Q = Q
      simp [Q, heteroKron_mul, (conjIsometry_one_isProj phiA).isIdempotentElem.eq]
    · change star Q = Q
      simp only [Q, Matrix.star_eq_conjTranspose, heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        (conjIsometry_one_isProj phiA).isSelfAdjoint.isHermitian.eq])
    (isometryTensor phiA phiB psi) delta (by
      dsimp only [Q]
      rw [applyOperatorToState_leftTensor_conjIsometry, heteroKron_one_one,
        applyOperatorToState_one])
  simp only [hcompression] at hbound
  exact hbound

/-- Bob's isometry transfer on a bipartite comparison state, with the same
state error and constants independent of the answer count as Alice's transfer.
This is blueprint `thm:pauli-isometry-transfer-bob-support`, the second
operator comparison needed in the proof of `thm:pauli`. -/
theorem sum_norm_rightTensor_conjIsometry_sub_sq_le
    (M : α → Op ιB) (N : MIPStarRE.Quantum.Measurement α κB)
    (T : α → Op (κA × κB))
    (hintertwine : ∀ a : α,
      N.effect a * isometryMatrix phiB = isometryMatrix phiB * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a : α, ‖applyOperatorToState
        (heteroKron 1 (conjIsometry phiB (M a)) - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (heteroKron 1 (N.effect a) - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron 1 (conjIsometry phiB 1)
  have hcompression (a : α) : (rightPlacedMeasurement N).effect a * Q =
      heteroKron 1 (conjIsometry phiB (M a)) := by
    change heteroKron 1 (N.effect a) * heteroKron 1 _ = _
    simp [heteroKron_mul, mul_conjIsometry_one_eq phiB (hintertwine a)]
  have hbound := sum_norm_mul_projection_sub_sq_le (rightPlacedMeasurement N) T Q (by
    constructor
    · change Q * Q = Q
      simp [Q, heteroKron_mul, (conjIsometry_one_isProj phiB).isIdempotentElem.eq]
    · change star Q = Q
      simp only [Q, Matrix.star_eq_conjTranspose, heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        (conjIsometry_one_isProj phiB).isSelfAdjoint.isHermitian.eq])
    (isometryTensor phiA phiB psi) delta (by
      dsimp only [Q]
      rw [applyOperatorToState_rightTensor_conjIsometry, heteroKron_one_one,
        applyOperatorToState_one])
  simp only [hcompression] at hbound
  exact hbound

end MIPStarRE.QPBT
