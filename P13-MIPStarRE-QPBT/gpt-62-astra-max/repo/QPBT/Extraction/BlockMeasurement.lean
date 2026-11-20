module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.PointConsistencyPrime

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

variable {X : Type*} (side : PlayerSide) {α : Type*} [Fintype α]
  (A : Measurement α (ExtractionBlock P (S.LocalSpace side)))

/-- Place a complete measurement on a player's full extraction block. -/
def blockMeasurement :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  refine Measurement.ofSumEqOne (fun a => S.placeSide side (A.effect a)) ?_ ?_
  · intro a
    cases side
    · exact reindexOp_nonneg _ (kronecker_nonneg (A.pos a) Matrix.PosSemidef.one.nonneg)
    · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (A.pos a))
  · cases side
    · rw [← S.placeSide_alice_finset_sum, A.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]
    · rw [← S.placeSide_bob_finset_sum, A.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]

/-- The effects of a block measurement use the existing block placement. -/
@[simp] theorem blockMeasurement_effect (a : α) :
    (S.blockMeasurement side A).effect a = S.placeSide side (A.effect a) := rfl

/-- Placing a projective measurement on an extraction block preserves projectivity. -/
theorem blockMeasurement_isProjective
    (hA : Measurement.IsProjective A) :
    Measurement.IsProjective (S.blockMeasurement side A) := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · convert (reindexMeasurement_isProjective e (leftPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker (hA a)
      (IsStarProjection.one _))) using 1
    rfl
  · convert (reindexMeasurement_isProjective e (rightPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker
      (IsStarProjection.one _) (hA a))) using 1
    rfl

/-- Original-register quadratic forms are unchanged by adjoining the two EPR
pairs. -/
theorem stateQForm_placePlayers (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    stateQForm S.psiHat (S.placePlayer .alice A * S.placePlayer .bob B) =
      stateQForm S.toStrategy.ψ (heteroKron A 1 * heteroKron 1 B) := by
  letI : DecidableEq (((S.toStrategy.ιA × S.toStrategy.ιB) ×
      (PauliRegister P × PauliRegister P)) × (PauliRegister P × PauliRegister P)) :=
    instDecidableEqProd
  have hAB := heteroKron_isHermitian hA hB
  change stateQForm S.psiHat
    (S.place .AA' _ * S.place .BB' (heteroKron B 1)) = _
  rw [S.psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    WinImplications.reindexOp_mul, S.reindexOp_sixRegShuffle_place_AA'_heteroKron,
    S.reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp [heteroKron_mul, heteroKron_one_one]
  rw [stateQForm_vecTensor_heteroKron _ _ _ _
    (heteroKron_isHermitian (A := _) (B := _) hAB Matrix.isHermitian_one) Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    DistanceCalculus.stateQForm_one, eprState_norm]
  ring

/-- Adjoining the two EPR pairs preserves the consistency defect between
families of original-register measurements. -/
theorem consistencyDefect_placePlayers [DecidableEq α]
    [Fintype X] [DecidableEq X]
    (mu : Distribution X) (A : X → Measurement α S.toStrategy.ιA)
    (B : X → Measurement α S.toStrategy.ιB) :
    consistencyDefect mu (fun x a => S.placePlayer .alice ((A x).effect a))
        (fun x a => S.placePlayer .bob ((B x).effect a)) S.psiHat =
      bipartiteDefect mu A
        B S.toStrategy.ψ := by
  simp [bipartiteDefect]
  apply avgOver_congr
  intro x
  congr 1 with a
  congr 1 with b
  by_cases hab : a = b
  · simp_all
  · simp_all
    exact S.stateQForm_placePlayers _ _
      (measurement_effect_hermitian (A x) a)
      (measurement_effect_hermitian (B x) b)

end ProjectiveSetting

end

end MIPStarRE.QPBT
