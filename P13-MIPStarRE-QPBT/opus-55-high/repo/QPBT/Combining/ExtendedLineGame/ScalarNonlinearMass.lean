module

public import QPBT.Combining.ExtendedLineGame.ScalarPolynomial
public import QPBT.Combining.PolynomialImageBounds

/-!
# Scalar-nonlinear mass of the actual rounded measurements

The full polynomial-outcome ordered estimate is composed with the concentration
bound for scalar-nonlinear outcomes. Opposite placements commute; no symmetry of the
player spaces is required. Projectivity retains the actual outcome masses.

## References

`eq:qld-g-42`, `eq:qld-g-prime`, and `eq:qld-g-prime-bound`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1326`.
This is only scalar-linearity concentration; the variable-separation estimates
and retained overlaps are separate results.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {ε : ℝ}

/-- Actual mass of outcomes outside `alpha*g1(x,z) + beta*g2(x,z)`. The
coefficients may still depend on both base blocks. -/
def scalarNonlinearMass (S : ProjectiveSetting P ε) (p : Placement)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => ¬ ∃ r t : MvPolynomial (Fin (2 * P.m))
      (PauliScalar P), scalarPolynomial P g =
        MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

theorem placed_orderedIndicator (S : ProjectiveSetting P ε) (p : Placement) (x : ExtendedPointQuestion P)
    (a : PauliScalar P) :
    orderedIndicator (S.placedMeasurement p (S.pointMeasExp p.side .X x.1.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z x.1.2)) x.2.1 x.2.2 a =
    S.place p (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
        x.2.1 * ab.1 + x.2.2 * ab.2 = a),
      (S.pointMeasExp p.side .X x.1.1).effect ab.1 *
        (S.pointMeasExp p.side .Z x.1.2).effect ab.2) := by
  rw [S.place_finsetSum, Finset.sum_filter]
  simp [orderedIndicator, ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]

/-- Opposite placements commute, identifying the residual on the actual
projected state with the ordered-error residual. This supports both orders
of `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
theorem placed_residual (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Op (S.ExpandedLocalSpace p1.side)) (T : Op (S.ExpandedLocalSpace p2.side)) :
    applyOperatorToState (S.place p1 R) S.psiHat -
      applyOperatorToState (S.place p2 T)
        (applyOperatorToState (S.place p1 R) S.psiHat) =
      applyOperatorToState (S.place p1 R * (1 - S.place p2 T)) S.psiHat := by
  rw [← applyOperatorToState_mul, ← S.place_comm p1 p2 hopposite R T, mul_sub, mul_one]
  simp [applyOperatorToState, map_sub, LinearMap.sub_apply]

/-- The scalar-nonlinear outcome mass is bounded by twice the actual full
ordered error plus `2*((2m+2)d+1)/q`. All transports and degree bounds are
derived internally from the actual singleton outcomes. This auxiliary applies
to every opposite placement of a complete projective measurement. -/
theorem scalarNonlinearMass_le_ordered_error (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    scalarNonlinearMass S p1 R ≤ 2 * extendedPolynomialOrderedError S p1 p2 R false +
      2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
  classical
  let s := Finset.univ.filter (fun g => ¬ ∃ r t : MvPolynomial (Fin (2 * P.m))
      (PauliScalar P), scalarPolynomial P g =
        MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
  let ψ := fun g => applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side .X (fun i => u ((baseCoordinateEquiv P.m).symm (.inl i))))
  let Z := fun u : Fin (2 * P.m) → PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side .Z (fun i => u ((baseCoordinateEquiv P.m).symm (.inr i))))
  have hX : ∀ u, Measurement.IsProjective (X u) := fun u =>
    S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)
  have hZ : ∀ u, Measurement.IsProjective (Z u) := fun u =>
    S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _)
  have h := nonlinear_mass_le_ordered_error s (scalarPolynomial P)
    (fun g hg => (Finset.mem_filter.mp hg).2) X Z hX hZ ψ
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      sum_projective_state_norm_sq (S.placedMeasurement p1 R)
        (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hdegree : (∑ g ∈ s,
      (((scalarPolynomial P g).support.sup fun e =>
          ((scalarPolynomial P g).coeff e).totalDegree) +
        max 1 (scalarPolynomial P g).totalDegree + 1 : ℕ) /
          (Fintype.card (PauliScalar P) : ℝ) * ‖ψ g‖ ^ 2) ≤
      (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
    have hcard : Fintype.card (PauliScalar P) = P.q :=
      @FieldModel.card P.q P.model.toFieldModel
    rw [hcard]
    refine (Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast scalarPolynomial_degree_term_le P g :
        (_ : ℝ) ≤ ((2 * P.m + 2) * P.d + 1 : ℕ))
        (Nat.cast_nonneg _)) (sq_nonneg _)).trans (le_of_le_of_eq
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity)
      (by rw [← Finset.mul_sum, hmass, mul_one]))
  let f := fun (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) g =>
    ‖ψ g - applyOperatorToState (orderedIndicator (X u) (Z u) (v 0) (v 1)
      (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
        (scalarPolynomial P g)))) (ψ g)‖ ^ 2
  have hfull : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g, f u v g)) =
        extendedPolynomialOrderedError S p1 p2 R false := by
    rw [← avgOver_uniform_prod (fun u v => ∑ g, f u v g), extendedPolynomialOrderedError,
      avgOver_uniform_equiv (scalarBaseQuestionEquiv P).symm]
    refine avgOver_congr _ _ _ fun ⟨u, v⟩ => Finset.sum_congr rfl fun g _ => ?_
    dsimp only [f]
    rw [scalarPolynomial_eval]
    have hXZ : orderedIndicator (X u) (Z u) (v 0) (v 1)
        (extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g) =
        orderedIndicator
          (S.placedMeasurement p2 (S.pointMeasExp p2.side .X
            (scalarBaseQuestionEquiv P (u, v)).1.1))
          (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z
            (scalarBaseQuestionEquiv P (u, v)).1.2))
          (scalarBaseQuestionEquiv P (u, v)).2.1
          (scalarBaseQuestionEquiv P (u, v)).2.2
          (extendedPolynomialRead P (scalarBaseQuestionEquiv P (u, v)) g) := by
      simp [X, Z, scalarBaseQuestionEquiv, Equiv.piCongrLeft_apply]
    rw [hXZ, placed_orderedIndicator]
    exact congrArg (‖·‖ ^ 2) (placed_residual S p1 p2 hopposite _ _)
  have herror : avgOver (uniformDistribution (Fin (2 * P.m) → PauliScalar P)) (fun u =>
      avgOver (uniformDistribution (Fin 2 → PauliScalar P)) (fun v => ∑ g ∈ s, f u v g)) ≤
        extendedPolynomialOrderedError S p1 p2 R false := by
    exact hfull ▸ avgOver_mono _ _ _ fun u => avgOver_mono _ _ _ fun v =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  grind [scalarNonlinearMass]

end ExtendedLineGame

end

end MIPStarRE.QPBT
