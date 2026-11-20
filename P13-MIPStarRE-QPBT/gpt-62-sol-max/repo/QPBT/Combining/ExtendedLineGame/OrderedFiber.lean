module

public import QPBT.Combining.ExtendedLineGame.ScalarPolynomial
public import QPBT.Combining.PolynomialImageBounds

/-! # Residuals in ordered fiber coordinates

The nonlinear, wrong-variable, and retained-point estimates all test the
same projected vectors against the same ordered point effects. -/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

variable {P : AdmissibleParams} {ε : ℝ}

/-- The projected vector for one outcome of the rounded polynomial measurement. -/
abbrev polyOutcomeState (S : ProjectiveSetting P ε) (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side))
    (g : ExtendedPoly P) :=
  applyOperatorToState (S.place p (R.effect g)) S.psiHat

/-- The rounded measurement's projected vectors have total squared norm one. -/
theorem polyOutcomeState_norm_sum (S : ProjectiveSetting P ε) (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side))
    (hR : Measurement.IsProjective R) : ∑ g, ‖polyOutcomeState S p R g‖ ^ 2 = 1 := by
  simpa only [polyOutcomeState, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow]
    using sum_projective_state_norm_sq (S.placedMeasurement p R)
      (S.placedMeasurement_isProjective p R hR) S.psiHat

/-- A subset of projected vectors contributes at most the uniform bound on its weights. -/
theorem polyOutcomeState_weight_bound (S : ProjectiveSetting P ε) (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side))
    (hR : Measurement.IsProjective R) (s : Finset (ExtendedPoly P))
    (C : ℝ) (hC : 0 ≤ C) : ∑ g ∈ s, C * ‖polyOutcomeState S p R g‖ ^ 2 ≤ C := by
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left ?_ hC).trans_eq (mul_one C)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => sq_nonneg _)).trans_eq (polyOutcomeState_norm_sum S p R hR)

/-- A point readout on a selected placement. -/
abbrev placedPoint (S : ProjectiveSetting P ε) (p : Placement) (W : PauliKind)
    (x : PauliPoint P) :=
  S.placedMeasurement p (S.pointMeasExp p.side W x)

theorem placedPoint_projective (S : ProjectiveSetting P ε) (p : Placement) (W : PauliKind)
    (x : PauliPoint P) : Measurement.IsProjective (placedPoint S p W x) :=
  S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _)

/-- Acting on a projected vector by the ordered sum of the compatible point effects. -/
abbrev fiberImage (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) (z x : PauliPoint P) (v : Fin 2 → PauliScalar P)
    (g : ExtendedPoly P) :=
  applyOperatorToState (orderedIndicator
    (placedPoint S p2 W x)
    (placedPoint S p2 W.other z) (v 0) (v 1)
    (extendedPolynomialRead P (fiberQuestionEquiv P W ((z, x), v)) g))
    (polyOutcomeState S p1 R g)

/-- Average first over the two scalar coefficients, then over the two base blocks. -/
abbrev fiberAverage (P : AdmissibleParams)
    (f : PauliPoint P → PauliPoint P → (Fin 2 → PauliScalar P) → ℝ) :=
  avgOver (uniformDistribution _) fun z => avgOver (uniformDistribution _) fun x =>
    avgOver (uniformDistribution _) (f z x)

theorem fiberAverage_mono {f g : PauliPoint P → PauliPoint P → (Fin 2 → PauliScalar P) → ℝ}
    (h : ∀ z x v, f z x v ≤ g z x v) : fiberAverage P f ≤ fiberAverage P g :=
  avgOver_mono _ _ _ fun z => avgOver_mono _ _ _ fun x => avgOver_mono _ _ _ (h z x)

/-- Exact placement and order transport for the common joint scalar sample.
This also transports the retained-overlap calculation in `lem:qld-4-7`. -/
theorem placed_fiber_orderedIndicator {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) (W : PauliKind)
    (x z : PauliPoint P) (v : Fin 2 → PauliScalar P) (a : PauliScalar P) :
    orderedIndicator
      (S.placedMeasurement p (S.pointMeasExp p.side W x))
      (S.placedMeasurement p (S.pointMeasExp p.side W.other z))
      (v 0) (v 1) a =
    S.place p (S.extendedPointProduct p.side W
      (fiberQuestionEquiv P W ((z, x), v)) a) := by
  rw [ProjectiveSetting.extendedPointProduct, pointAffinePostprocess,
    S.place_finsetSum, Finset.sum_filter]
  simp only [orderedIndicator, ProjectiveSetting.placedMeasurement_effect]
  cases W
  · simp [fiberQuestionEquiv, ExtendedPointQuestion.read, PauliKind.pairOrder, ProjectiveSetting.place_mul, PauliKind.other, ProjectiveSetting.pointPairEffect, PauliKind.component]
  · apply Fintype.sum_equiv (Equiv.prodComm (PauliScalar P) (PauliScalar P))
    intro ab
    simp [fiberQuestionEquiv, ExtendedPointQuestion.read, PauliKind.pairOrder, add_comm, ProjectiveSetting.place_mul,
      PauliKind.other, ProjectiveSetting.pointPairEffect, PauliKind.component]

/-- Opposite placements commute, identifying the residual on the actual
projected state with the ordered-error residual. This supports both orders
of `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
theorem placed_residual {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Op (S.ExpandedLocalSpace p1.side)) (T : Op (S.ExpandedLocalSpace p2.side)) :
    applyOperatorToState (S.place p1 R) S.psiHat -
      applyOperatorToState (S.place p2 T)
        (applyOperatorToState (S.place p1 R) S.psiHat) =
      applyOperatorToState (S.place p1 R * (1 - S.place p2 T)) S.psiHat := by
  rw [← applyOperatorToState_mul, ← S.place_comm p1 p2 hopposite R T, mul_sub, mul_one]
  simp [applyOperatorToState]

/-- The full residual is exactly the ordered error after the joint reindexing. -/
theorem fiberResidual_eq_orderedError (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side)) (W : PauliKind) :
    fiberAverage P (fun z x v => ∑ g,
      ‖polyOutcomeState S p1 R g - fiberImage S p1 p2 R W z x v g‖ ^ 2) =
      extendedPolynomialOrderedError S p1 p2 R W := by
  let f (z x : PauliPoint P) (v : Fin 2 → PauliScalar P) :=
    ∑ g, ‖polyOutcomeState S p1 R g - fiberImage S p1 p2 R W z x v g‖ ^ 2
  change fiberAverage P f = _
  unfold fiberAverage extendedPolynomialOrderedError
  rw [← avgOver_uniform_prod (fun z x => avgOver (uniformDistribution _) (f z x)),
    ← avgOver_uniform_prod (fun zx : PointPair P =>
      fun v => f zx.1 zx.2 v),
    avgOver_uniform_equiv (fiberQuestionEquiv P W).symm]
  simp_all [f, fiberImage, placedPoint, polyOutcomeState, placed_fiber_orderedIndicator, placed_residual S p1 p2 hopposite, Equiv.symm_symm]

/-- Restricting the outcome sum can only decrease the ordered residual. -/
theorem fiberResidual_le_orderedError (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side)) (W : PauliKind)
    (s : Finset (ExtendedPoly P)) :
    fiberAverage P (fun z x v => ∑ g ∈ s,
      ‖polyOutcomeState S p1 R g - fiberImage S p1 p2 R W z x v g‖ ^ 2) ≤
      extendedPolynomialOrderedError S p1 p2 R W := by
  rw [← fiberResidual_eq_orderedError S p1 p2 hopposite R W]
  exact fiberAverage_mono fun z x v => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun _ _ _ => sq_nonneg _

/-- A low image norm bounds the mass of a class of outcomes by its ordered
residual and the uniform image bound. -/
theorem polyOutcomeMass_le_orderedError (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (W : PauliKind)
    (s : Finset (ExtendedPoly P)) (C : ℝ) (hC : 0 ≤ C)
    (himage : ∀ g ∈ s, fiberAverage P (fun z x v => ‖fiberImage S p1 p2 R W z x v g‖ ^ 2)
      ≤ C * ‖polyOutcomeState S p1 R g‖ ^ 2) :
    ∑ g ∈ s, ‖polyOutcomeState S p1 R g‖ ^ 2 ≤
      2 * extendedPolynomialOrderedError S p1 p2 R W + 2 * C := by
  let A := fiberImage S p1 p2 R W
  have havg := fiberAverage_mono fun z x v =>
    sum_mass_le_residual_add_image s (polyOutcomeState S p1 R) (A z x v)
  have hnorm : fiberAverage P (fun z x v => ∑ g ∈ s, ‖A z x v g‖ ^ 2) ≤ C := by
    simp_rw [fiberAverage, avgOver_finset_sum]
    exact (Finset.sum_le_sum himage).trans (polyOutcomeState_weight_bound S p1 R hR s C hC)
  have hres := fiberResidual_le_orderedError S p1 p2 hopposite R W s
  simp only [fiberAverage, avgOver_uniform_const, avgOver_add, avgOver_const_mul] at havg hnorm hres
  linarith only [havg, hres, hnorm]

end

end MIPStarRE.QPBT.ExtendedLineGame
