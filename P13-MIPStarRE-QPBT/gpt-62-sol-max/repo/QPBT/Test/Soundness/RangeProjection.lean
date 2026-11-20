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

/-- Intertwining identifies isometry conjugation with insertion of its range projection. -/
private theorem mul_conjIsometry_one_eq {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : Op ι) (N : Op κ)
    (hintertwine : N * isometryMatrix phi = isometryMatrix phi * M) :
    N * conjIsometry phi 1 = conjIsometry phi M := by
  rw [conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hintertwine]
  rfl

/-- Reindexing twice along inverse equivalences restores the operator. -/
theorem reindexOp_symm_cancel {ι κ : Type*} (e : ι ≃ κ) (T : Op ι) :
    reindexOp e (reindexOp e.symm T) = T := by
  ext i j
  simp [reindexOp, Matrix.reindex_apply]

/-- The complementary projection kills a fixed vector and contracts its displacement. -/
theorem norm_one_sub_proj_apply_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Op ι} (hQ : IsProj Q) {θ : EuclideanSpace ℂ ι} (hfix : applyOperatorToState Q θ = θ)
    (ξ : EuclideanSpace ℂ ι) : ‖applyOperatorToState (1 - Q) ξ‖ ^ 2 ≤ ‖ξ - θ‖ ^ 2 := by
  have h := norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (ξ - θ)
  have hzero : applyOperatorToState (1 - Q) θ = 0 := by
    rw [applyOperatorToState_sub_op, applyOperatorToState_one, hfix, sub_self]
  rw [applyOperatorToState_sub, hzero, sub_zero] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

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
  have hsum := (sum_norm_mul_apply_le N.effect (1 - Q) delta
    (MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one N)).trans
    (norm_one_sub_proj_apply_sq_le hQ htheta delta)
  have hsplit (a : α) : N.effect a * Q - T a = (N.effect a - T a) - N.effect a * (1 - Q) := by
    noncomm_ring
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset α)) fun a _ => by
    have h := parallelogram_law_with_norm ℂ (applyOperatorToState (N.effect a - T a) delta)
      (applyOperatorToState (N.effect a * (1 - Q)) delta)
    have hz := sq_nonneg ‖applyOperatorToState (N.effect a - T a) delta +
      applyOperatorToState (N.effect a * (1 - Q)) delta‖
    refine (show ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2 +
        2 * ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2 from ?_)
    rw [hsplit, applyOperatorToState_sub_op]
    linarith
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  linarith

section

variable {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
include α ιA ιB κA κB phiA phiB

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
  have hQ : IsProj Q := isProj_leftTensor (isProj_conjIsometry_one phiA)
  have hfix : applyOperatorToState Q (isometryTensor phiA phiB psi) =
      isometryTensor phiA phiB psi := by
    dsimp only [Q]
    rw [applyOperatorToState_leftTensor_conjIsometry, heteroKron_one_one,
      applyOperatorToState_one]
  have hcompression (a : α) : (leftPlacedMeasurement N).effect a * Q =
      heteroKron (conjIsometry phiA (M a)) 1 := by
    change heteroKron (N.effect a) 1 * heteroKron (conjIsometry phiA 1) 1 = _
    rw [heteroKron_mul, Matrix.one_mul,
      mul_conjIsometry_one_eq phiA (M a) (N.effect a) (hintertwine a)]
  have hbound := sum_norm_mul_projection_sub_sq_le (leftPlacedMeasurement N) T Q hQ
    (isometryTensor phiA phiB psi) delta hfix
  simp only [hcompression] at hbound
  simpa only [leftPlacedMeasurement_effect] using hbound

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
  let e := Equiv.prodComm ιA ιB
  let f := Equiv.prodComm κA κB
  simpa only [e, f, norm_applyOperatorToState_reindexState, reindexOp_sub,
    reindexOp_prodComm_heteroKron, reindexOp_symm_cancel, isometryTensor_prodComm,
    norm_reindexState_sub_eq] using
    sum_norm_leftTensor_conjIsometry_sub_sq_le phiB phiA M N (fun a => reindexOp f.symm (T a))
      hintertwine (reindexState e psi) (reindexState f delta)

end

end MIPStarRE.QPBT
