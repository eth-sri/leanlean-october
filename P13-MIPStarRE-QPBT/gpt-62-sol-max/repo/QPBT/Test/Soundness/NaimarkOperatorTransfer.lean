module

public import QPBT.Test.Soundness.NaimarkReduction
public import QPBT.Test.Soundness.RangeProjection
public import QPBT.Test.Soundness.PlayerExchange
public import QPBT.Games.EPR
public import QPBT.Observables.ExpandedDefs

/-!
# Pauli operator transfer through Naimark compression

The questionwise Naimark dilation preserves the complete Pauli readout only
after ground-slice compression.  This module proves the corresponding
state-dependent transfer for both players.  The range projection is retained
on both sides of every dilated effect, and the opposite ideal Pauli family is
used on the EPR state to control the second range defect.

## References

This is a formalization-only support result for `thm:pauli`, whose source
statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The projective reduction and the final isometry passage are at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
The omitted range-projection calculation is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#604.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

private theorem naimark_norm_add_three_sq_le {ι : Type*} [Fintype ι]
    (x y z : EuclideanSpace ℂ ι) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (show ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ from norm_add₃_le) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

private theorem sum_norm_compression_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T R : α → Op ι) (Q : Op ι) (hQ : IsProj Q)
    (hN : ∑ a, (N a)ᴴ * N a ≤ 1) (hR : ∑ a, (R a)ᴴ * R a ≤ 1)
    (theta delta : EuclideanSpace ℂ ι)
    (hfix : applyOperatorToState Q theta = theta)
    (hmirror : ∀ a, applyOperatorToState (T a) delta =
      applyOperatorToState (R a) delta)
    (hcomm : ∀ a, Q * R a = R a * Q) :
    ∑ a, ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (∑ a, ‖applyOperatorToState (N a - T a) delta‖ ^ 2) +
        6 * ‖delta - theta‖ ^ 2 := by
  have hcontract (v : EuclideanSpace ℂ ι) :
      ‖applyOperatorToState Q v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hrange := norm_one_sub_proj_apply_sq_le hQ hfix delta
  have hn := (sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrange
  have hr := (sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrange
  have hpoint (a : α) :
      ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
        3 * (‖applyOperatorToState (N a - T a) delta‖ ^ 2 +
          ‖applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
          ‖applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a =
        Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by
      noncomm_ring
    have hm : applyOperatorToState ((1 - Q) * T a) delta =
        applyOperatorToState (R a * (1 - Q)) delta := by
      rw [applyOperatorToState_mul, hmirror]
      rw [← applyOperatorToState_mul]
      congr 1
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    rw [hs, applyOperatorToState_sub_op, applyOperatorToState_sub_op]
    rw [hm, applyOperatorToState_mul, applyOperatorToState_mul,
      sub_eq_add_neg, sub_eq_add_neg]
    have h := naimark_norm_add_three_sq_le
      (applyOperatorToState Q (applyOperatorToState (N a - T a) delta))
      (-applyOperatorToState Q (applyOperatorToState (N a * (1 - Q)) delta))
      (-applyOperatorToState (R a * (1 - Q)) delta)
    simp only [norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontract _) (hcontract _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

private theorem idealState_pauli_mirror (P : AdmissibleParams)
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (aux : EuclideanSpace ℂ (I × J)) (W : PauliKind) (h : PauliRegister P) :
    applyOperatorToState (pauliProjOnA'' P W h) (idealState P aux) =
      applyOperatorToState (pauliProjOnB'' P W h) (idealState P aux) :=
  extracted_epr_actions_eq aux _ (pauliProj_transpose W h)

private theorem naimark_conjIsometry_compressed {ι α κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : Op (ι × Option α)) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) (naimarkCompression N) =
      conjIsometry φ (groundProjection ι α) * conjIsometry φ N *
        conjIsometry φ (groundProjection ι α) := by
  rw [conjIsometry_comp_naimarkEmbedding, naimarkInflation_naimarkCompression,
    conjIsometry_mul, conjIsometry_mul]

/-- Ground-slice compression of a dilated POVM in the first tensor factor. The
opposite measurement mirrors the target family on the comparison state. -/
private theorem naimark_left_compression_le {α β ι κ I J : Type}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ I)
    (θ : EuclideanSpace ℂ (κ × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ J)
    (M : Measurement β (ι × Option α)) (R : Measurement β J) (T : β → Op (I × J))
    (ψ : EuclideanSpace ℂ (ι × κ)) (ξ : EuclideanSpace ℂ (I × J))
    (hmirror : ∀ a, applyOperatorToState (T a) ξ =
      applyOperatorToState (heteroKron 1 (R.effect a)) ξ) :
    ∑ a, ‖applyOperatorToState (heteroKron
        (conjIsometry (φ.comp (naimarkEmbedding ι α)) (naimarkCompression (M.effect a))) 1 - T a) ξ‖ ^ 2 ≤
      3 * (∑ a, ‖applyOperatorToState (heteroKron (conjIsometry φ (M.effect a)) 1 - T a) ξ‖ ^ 2) +
        6 * ‖isometryTensor φ θ (naimarkDilatedState α ψ) - ξ‖ ^ 2 := by
  let Q : Op (I × J) := heteroKron (conjIsometry φ (groundProjection ι α)) 1
  let N := fun a => heteroKron (conjIsometry φ (M.effect a)) (1 : Op J)
  let χ := isometryTensor φ θ (naimarkDilatedState α ψ)
  have hfix : applyOperatorToState Q χ = χ := by
    dsimp only [Q, χ]
    rw [applyOperatorToState_leftTensor_conjIsometry,
      applyOperatorToState_leftTensor_groundProjection]
  have hcomm (a : β) : Q * heteroKron 1 (R.effect a) = heteroKron 1 (R.effect a) * Q := by
    simp only [Q, heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have h := sum_norm_compression_sub_sq_le N T (fun a => heteroKron 1 (R.effect a)) Q
    (isProj_leftTensor (isProj_conjIsometry φ (isProj_groundProjection ι α)))
    (leftTensor_sum_adjoint_mul_le_one
      (conjIsometry_sum_adjoint_mul_le_one φ (measurement_sum_adjoint_mul_le_one M)))
    (measurement_sum_adjoint_mul_le_one (rightPlacedMeasurement R)) χ ξ hfix hmirror hcomm
  simpa only [Q, N, χ, heteroKron_mul, Matrix.one_mul, naimark_conjIsometry_compressed,
    norm_sub_rev ξ] using h

section

variable (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind)
include P S w W

set_option maxHeartbeats 800000 in
-- Finite-register matrix algebra and nested finite sums make this proof
-- expensive to elaborate.
/-- Alice's complete Pauli operator-family distance after Naimark pullback is
at most three times the dilated distance plus six times the squared state error.
This is a Lean-only support theorem for the source proof; its witness is an
explicit actual witness on the constructed dilation. -/
theorem pauli_naimark_operator_distanceA_le :
    pauliOperatorDistanceA P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let M := ((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess pauliAnswerOrZero
  let ξ := idealState P w.aux
  let R := rightPlacedMeasurement (ιA := w.ιB') (pauliRegisterMeas (params := P) W)
  have hc (h : PauliRegister P) : naimarkCompression (M.effect h) =
      ((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h :=
    congrArg (fun M => M.effect h) (pauliNaimarkStrategy_pauli_compressA P S W)
  have h := naimark_left_compression_le w.φA w.φB M R (pauliProjOnA'' P W) S.ψ ξ (fun a => by
    rw [idealState_pauli_mirror P w.aux W a, pauliProjOnB'']
    rfl)
  simp_rw [hc] at h
  have hp : (pauliNaimarkStrategy P S).ψ = naimarkDilatedState (PauliAnswer P) S.ψ :=
    pauliNaimarkStrategy_state P S
  rw [hp]
  simpa only [M, ξ, pauliOperatorDistanceA, liftedAEffect,
    pauliNaimarkEmbeddingA] using! h

set_option maxHeartbeats 800000 in
-- The symmetric finite-register matrix calculation likewise requires extra
-- elaboration heartbeats.
/-- Bob's complete Pauli operator-family distance after Naimark pullback has
the same dimension-independent bound as Alice's. -/
theorem pauli_naimark_operator_distanceB_le :
    pauliOperatorDistanceB P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let G := pauliBasisTestSymm P
  let S' : Strategy (pauliBasisTest P) := G.swapStrategy S
  let v : PauliSoundnessWitness P (pauliNaimarkStrategy P S') := { w.swap with φA := w.φB }
  have h := pauli_naimark_operator_distanceA_le P S' v W
  have hψ : (pauliNaimarkStrategy P S').ψ = (G.swapStrategy (pauliNaimarkStrategy P S)).ψ := by
    rw [pauliNaimarkStrategy_state]
    change naimarkDilatedState (PauliAnswer P) (reindexState (Equiv.prodComm _ _) S.ψ) =
      reindexState (Equiv.prodComm _ _) (pauliNaimarkStrategy P S).ψ
    rw [pauliNaimarkStrategy_state, naimarkDilatedState_prodComm]
    rfl
  change pauliOperatorDistanceA P S' (pauliNaimarkWitness P S w).swap W ≤
    3 * pauliOperatorDistanceA P (G.swapStrategy (pauliNaimarkStrategy P S)) w.swap W +
      6 * ‖isometryTensor w.swap.φA w.swap.φB (pauliNaimarkStrategy P S').ψ -
        idealState P w.swap.aux‖ ^ 2 at h
  dsimp only [S', G] at h hψ
  rwa [hψ, w.swap_state_error, w.swap_completed_distance,
    (pauliNaimarkWitness P S w).swap_completed_distance] at h

end

end

end MIPStarRE.QPBT
