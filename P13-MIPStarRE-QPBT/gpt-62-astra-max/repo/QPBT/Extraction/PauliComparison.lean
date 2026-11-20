module

public import QPBT.Extraction.OverlapTransfer
public import QPBT.Extraction.EncodingSupport
public import QPBT.Extraction.Defs
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer

/-!
# Total Pauli comparison on a normalized ideal state

The complete answer-summed distance is controlled by the evaluated overlap on
another normalized state, the Schwartz--Zippel collision probability, and the
distance between the states. This is the operator comparison used after the
swap and auxiliary-state construction.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

section

variable {P : AdmissibleParams} {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J] (A : Measurement (PauliRegister P) (I × PauliRegister P)) [Fintype V]
  [DecidableEq V] (W : PauliKind) [Nonempty V] (aux : EuclideanSpace ℂ (I × J))

/-- A symmetric operator acts identically on the two halves of the extracted
EPR pair, including arbitrary auxiliary registers in local player order. -/
theorem extracted_epr_actions_eq (T : Op V) (hT : Tᵀ = T) :
    applyOperatorToState (heteroKron (heteroKron (1 : Op I) T) (1 : Op (J × V)))
        (reindexState prodShuffle (vecTensor aux (eprState V))) =
      applyOperatorToState (heteroKron (1 : Op (I × V)) (heteroKron (1 : Op J) T))
        (reindexState prodShuffle (vecTensor aux (eprState V))) := by
  ext p
  simp [applyOperatorToState, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [heteroKron, Matrix.kronecker, Matrix.one_apply, reindexState, vecTensor,
    eprState, prodShuffle, mul_ite, ite_mul, Prod.ext_iff, ite_and]
  rw [show T p.2.2 p.1.2 = T p.1.2 p.2.2 from congrFun (congrFun hT p.1.2) p.2.2]
  simp

/-- The full answer-summed Pauli distance on `aux tensor EPR` is at most twice
the evaluated-overlap deficit on `theta`, plus `2md/q` and four times the state
distance. The bound holds for every local POVM and every normalized auxiliary
state, with no restriction on the field, Pauli basis, or local dimensions.
This is the quantitative combination of paper `eq:qld-unitary-7` through
`eq:qld-unitary-9` and its following state-transfer estimate. -/
theorem pauli_distance_on_ideal_le (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × PauliRegister P) × (J × PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
    let B := rightPlacedMeasurement (ιA := J) (pauliRegisterMeas (params := P) W)
    (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron (A.effect h - heteroKron (1 : Op I) (pauliProj W h))
        (1 : Op (J × PauliRegister P))) ideal‖ ^ 2) ≤
      2 * (1 - avgOver (uniformDistribution (PauliPoint P)) (fun u =>
        ∑ a : PauliScalar P, stateQForm theta
          (heteroKron ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
            ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  dsimp only
  let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
  let B := rightPlacedMeasurement (ιA := J) (pauliRegisterMeas (params := P) W)
  have hideal : ‖ideal‖ = 1 := by
    rw [reindexState_norm_eq, vecTensor_norm_eq, haux, eprState_norm, one_mul]
  have hdist := point_distance_le_two_defect
    (leftPlacedMeasurement (ιB := J × PauliRegister P) A)
    (rightPlacedMeasurement (ιA := I × PauliRegister P) B) ideal
  simp [point_defect_eq, hideal] at hdist
  have haction (h : PauliRegister P) :
      applyOperatorToState
          (heteroKron (A.effect h - heteroKron 1 (pauliProj W h))
            1) ideal =
        applyOperatorToState
          ((leftPlacedMeasurement A).effect h -
            (rightPlacedMeasurement B).effect h) ideal := by
    change _ =
      applyOperatorToState (heteroKron (A.effect h) _ -
        heteroKron _ (heteroKron _ (pauliProj W h))) ideal
    rw [heteroKron_sub_left, DistanceCalculus.applyOperatorToState_sub_op,
      DistanceCalculus.applyOperatorToState_sub_op,
      extracted_epr_actions_eq aux _ (pauliProj_transpose W h)]
  rw [(Finset.sum_congr (s₁ := (Finset.univ : Finset (PauliRegister P)))
    rfl (fun h _ => congrArg (fun v => ‖v‖ ^ 2) (haction h)))]
  have hoverlap := by
                     have ht := evaluated_overlap_state_transfer A B
                       (fun h u => evalPoly (encodingPoly h) u) theta ideal htheta hideal
                     have hc := SandwichProduct.avg_diagonal_postprocess_stateQForm_le A B ideal
                       (fun h u => evalPoly (encodingPoly h) u) ((P.m * P.d : ℝ) / P.q) hideal
                       (by positivity) pauli_encoding_collision_le
                     exact ht.trans (add_le_add hc le_rfl)
  simp [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne, placed_product_stateQForm_eq] at hdist
  exact hdist.trans (by linarith)

end

/-- At construction error at most one, a universal extraction coefficient of
at least eighteen absorbs both the proved state error and the Pauli comparison
error. The collision term and fourth-root scale are exactly those of
`deltaExtract`; there is no parameter-dependent enlargement of the constant. -/
theorem extraction_small_error_absorption (C delta : ℝ) (m d q : ℕ)
    (hC : 18 ≤ C) (hdelta : 0 ≤ delta) (hdelta_one : delta ≤ 1) :
    16 * delta ≤ deltaExtract C delta m d q ∧
      2 * delta + 2 * (((m * d : ℕ) : ℝ) / q) + 16 * Real.sqrt delta ≤
        deltaExtract C delta m d q := by
  have hroot := Real.self_le_rpow_of_le_one hdelta hdelta_one
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hsqrt : Real.sqrt delta ≤ delta ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_one (by norm_num) (by norm_num)
  have hr : 0 ≤ (((m * d : ℕ) : ℝ) / q) := by positivity
  have hp := mul_le_mul_of_nonneg_right hC
    (add_nonneg (Real.rpow_nonneg hdelta (1 / 4)) hr)
  constructor
  · exact (show 16 * delta ≤ _ by nlinarith).trans hp
  · exact (show 2 * delta + 2 * ((m * d : ℕ) / q) + 16 * Real.sqrt delta ≤
      _ by nlinarith).trans hp

end

end MIPStarRE.QPBT
