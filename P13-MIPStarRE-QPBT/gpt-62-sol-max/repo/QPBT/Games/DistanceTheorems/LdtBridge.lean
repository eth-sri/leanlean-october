module

public import QPBT.Games.DistanceTheorems.TensorSupport
public import MIPStarRE.LDT.Test.StrategyRole.Algebra

/-! The LDT density and QPBT Euclidean formulations of consistency agree. -/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum DistanceCalculus
open scoped BigOperators MatrixOrder ComplexOrder

section

variable {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.LDT.Measurement alpha iota)
include alpha iota M

/-- Regard a complete LDT measurement as a matrix-valued QPBT
measurement, with exactly the same effects. -/
noncomputable def ldtMeasurementToMatrixMeasurement :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne M.outcome M.outcome_pos (by
    rw [M.sum_eq_total, M.total_eq_one])

@[simp] theorem ldtMeasurementToMatrixMeasurement_effect (a : alpha) :
    (ldtMeasurementToMatrixMeasurement M).effect a = M.outcome a :=
  rfl

end

/-- The pointwise LDT defect on complete measurements is the off-diagonal
Born mass of the vector representation of the state. -/
theorem ldt_qBipartiteConsDefect_eq {α I J : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty (I × J)]
    (ψ : PureState (I × J)) (A : LDT.Measurement α I) (B : LDT.Measurement α J) :
    qBipartiteConsDefect (ψ : QuantumState (I × J)) A.toSubMeas B.toSubMeas =
      ∑ a, ∑ b, if a = b then 0 else
        stateQForm (pureStateEuclideanVector ψ) (heteroKron (A.outcome a) (B.outcome b)) := by
  rw [qBipartiteConsDefect_of_measurements, ev_one_of_isNormalized _ ψ.toQuantumState_isNormalized]
  symm
  simpa only [qBipartiteMatchMass, ldtMeasurementToMatrixMeasurement_effect,
    pureStateEuclideanVector_norm, one_pow, pureState_stateQForm_eq_ev, heteroKron, opTensor] using
    point_placed_defect_eq (ldtMeasurementToMatrixMeasurement A)
      (ldtMeasurementToMatrixMeasurement B) (pureStateEuclideanVector ψ)

/-- Consistency for complete measurements has the same defect in both formulations. -/
theorem ldt_consRel_iff_consistencyDefect {X α I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty (I × J)]
    (ψ : PureState (I × J)) (μ : Distribution X)
    (A : X → MIPStarRE.LDT.Measurement α I) (B : X → MIPStarRE.LDT.Measurement α J) (δ : ℝ) :
    ConsRel (ψ : QuantumState (I × J)) μ (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) δ ↔
      consistencyDefect μ (fun x a => heteroKron ((A x).outcome a) 1)
        (fun x a => heteroKron 1 ((B x).outcome a)) (pureStateEuclideanVector ψ) ≤ δ := by
  have h : consistencyDefect μ (fun x a => heteroKron ((A x).outcome a) 1)
      (fun x a => heteroKron 1 ((B x).outcome a)) (pureStateEuclideanVector ψ) =
      bipartiteConsError (ψ : QuantumState (I × J)) μ
        (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) := by
    unfold consistencyDefect bipartiteConsError
    refine avgOver_congr _ _ _ fun x => ?_
    simp only [placed_product_stateQForm_eq,
      ldt_qBipartiteConsDefect_eq]
  rw [h]
  exact ⟨ConsRel.offDiagonalBound, fun h => ⟨h⟩⟩

end MIPStarRE.QPBT
