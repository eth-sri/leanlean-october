module

public import QPBT.Combining.Points.Consistency
public import QPBT.Games.DistanceTheorems
public import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Averaging

/-! # Orthonormalization of the sandwich measurements

Split the six registers at the selected placement and apply projective rounding
on that tensor factor. The average bound follows by Jensen's inequality for
the fourth root (paper `14_analysis_of_the_pauli_basis_test.tex:786-790`).
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

set_option synthInstance.maxSize 400

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (p : Placement)

private theorem round_sandwich_at (xz : PointPair P) :
    ∃ Q : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side),
      Measurement.IsProjective Q ∧
      (∑ ab, ‖applyOperatorToState (S.place p (Q.effect ab) -
        S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab)) S.psiHat‖ ^ 2) ≤
        220 * Real.rpow (S.sandwichDefectBound p (overlapPartner p) xz) (1 / 4 : ℝ) := by
  classical
  let q := overlapPartner p
  let A := S.sandwichPoint p.side xz.1 xz.2
  let B := leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
    (S.sandwichPoint q.side xz.1 xz.2)
  let ψ := reindexState (S.placeSplit p) S.psiHat
  let δ := S.sandwichDefectBound p q xz
  have hp : p.IsOpposite q := p.opposite_partner
  have hcons : bipartiteDefect (uniformDistribution Unit) (fun _ => A) (fun _ => B) ψ ≤ δ := by
    simpa only [bipartiteDefect, consistencyDefect, avgOver_uniform_const, A, B, ψ,
      leftPlacedMeasurement_effect, rightPlacedMeasurement_effect, stateQForm_reindexState,
      reindexOp_mul, ← S.place_eq_reindex, S.reindexOp_placeSplit_partner] using
      S.sandwich_offDiagonal_le_sandwichDefectBound p q hp xz
  obtain ⟨Q, hQ, hd⟩ := projective_rounding_with_explicit_constant ψ
    (by dsimp only [ψ]; rw [reindexState_norm_eq, S.psiHat_norm]) A B δ
    (S.sandwichDefectBound_nonneg p q xz) hcons
  refine ⟨Q, hQ, ?_⟩
  simpa only [opFamilyDistSq, avgOver_uniform_const, ψ, norm_applyOperatorToState_reindexState,
    reindexOp_sub, ← S.place_eq_reindex, A] using hd

/-- Fiberwise projective rounding of the sandwich POVM on the selected local space. -/
theorem exists_projective_close_sandwich :
    ∃ Q : PointPair P → Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side),
      (∀ xz, Measurement.IsProjective (Q xz)) ∧
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz ab => S.place p ((Q xz).effect ab))
        (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab)) S.psiHat ≤
      220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p (overlapPartner p))) (1 / 4 : ℝ) := by
  classical
  choose Q hQ hd using S.round_sandwich_at p
  refine ⟨Q, hQ, (avgOver_mono _ _ _ hd).trans ?_⟩
  rw [avgOver_const_mul]
  exact mul_le_mul_of_nonneg_left
    (MainInductionStep.avgOver_uniform_rpow_one_div_le_rpow_avg _ 4 (by decide)
      (S.sandwichDefectBound_nonneg p (overlapPartner p))) (by norm_num)

end ProjectiveSetting

end

end MIPStarRE.QPBT
