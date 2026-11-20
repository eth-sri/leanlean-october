module

public import QPBT.Extraction.Consistency

/-!
# Measurements on extraction blocks

This module places a complete measurement from either player's three-register
extraction block on the full six-register space. It also records the transport
of original-player consistency through the two adjoined EPR states.

## References

These are finite-dimensional placement lemmas supporting blueprint
`lem:qld-construct-the-paulis` and `lem:qld-unitary`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

/-- Place a measurement on the original register of either player. -/
def playerMeasurement {α : Type*} [Fintype α] :
    (side : PlayerSide) → Measurement α (S.LocalSpace side) →
      Measurement α (S.ExpandedSpace)
  | .alice, M => S.placedMeasurement .AA' (leftPlacedMeasurement M)
  | .bob, M => S.placedMeasurement .BB' (leftPlacedMeasurement M)

@[simp] theorem playerMeasurement_effect {α : Type*} [Fintype α] (side : PlayerSide)
    (M : Measurement α (S.LocalSpace side)) (a : α) :
    (S.playerMeasurement side M).effect a = S.placePlayer side (M.effect a) := by
  cases side <;> rfl

/-- Original-register quadratic forms are unchanged by adjoining the two EPR
pairs. -/
theorem stateQForm_placePlayers (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB) :
    stateQForm S.psiHat (S.placePlayer .alice A * S.placePlayer .bob B) =
      stateQForm S.toStrategy.ψ (heteroKron A 1 * heteroKron 1 B) := by
  rw [placed_product_stateQForm_eq]
  change S.placedCorrelation .AA' .BB' (heteroKron A 1) (heteroKron B 1) = _
  have h := S.stateQForm_psiHat_of_reindex (A := heteroKron A B) (B := 1) (C := 1)
    (M := S.place .AA' (heteroKron A 1) * S.place .BB' (heteroKron B 1))
    (by
      rw [reindexOp_mul, S.reindexOp_sixRegShuffle_place .AA' A 1,
        S.reindexOp_sixRegShuffle_place .BB' B 1]
      simp only [placeStrategySide, Placement.side, Placement.firstEpr, Placement.secondEpr,
        heteroKron_mul, one_mul, mul_one, heteroKron_one_one]) Matrix.isHermitian_one Matrix.isHermitian_one
  simpa only [stateQForm_one, eprState_norm, one_pow, mul_one] using h

/-- Adjoining the two EPR pairs preserves the consistency defect between
families of original-register measurements. -/
theorem consistencyDefect_placePlayers {X α : Type*} [Fintype α] [DecidableEq α]
    [Fintype X] [DecidableEq X]
    (mu : Distribution X) (A : X → Measurement α S.toStrategy.ιA)
    (B : X → Measurement α S.toStrategy.ιB) :
    consistencyDefect mu (fun x a => S.placePlayer .alice ((A x).effect a))
        (fun x a => S.placePlayer .bob ((B x).effect a)) S.psiHat =
      bipartiteDefect mu A
        B S.toStrategy.ψ := by
  simp_rw [consistencyDefect, stateQForm_placePlayers]

end ProjectiveSetting

end

end MIPStarRE.QPBT
