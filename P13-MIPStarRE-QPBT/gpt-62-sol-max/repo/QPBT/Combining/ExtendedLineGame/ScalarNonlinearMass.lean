module

public import QPBT.Combining.ExtendedLineGame.OrderedFiber

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

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)
include P ε S

/-- Actual mass of outcomes outside `alpha*g1(x,z) + beta*g2(x,z)`. The
coefficients may still depend on both base blocks. -/
def scalarNonlinearMass (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side)) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => ¬ ScalarLinear P g),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

/-- The scalar-nonlinear outcome mass is bounded by twice the actual full
ordered error plus `2*((2m+2)d+1)/q`. All transports and degree bounds are
derived internally from the actual singleton outcomes. This auxiliary applies
to every opposite placement of a complete projective measurement. -/
theorem scalarNonlinearMass_le_ordered_error (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    scalarNonlinearMass S p1 R ≤ 2 * extendedPolynomialOrderedError S p1 p2 R .X +
      2 * (((2 * P.m + 2) * P.d + 1 : ℕ) : ℝ) / P.q := by
  classical
  let s := Finset.univ.filter (fun g => ¬ ScalarLinear P g)
  rw [mul_div_assoc]
  refine polyOutcomeMass_le_orderedError S p1 p2 hopposite R hR .X s _ (by positivity) ?_
  intro g hg
  let e := (((baseCoordinateEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans
    (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => PauliScalar P)).trans (Equiv.prodComm _ _)
  let X := fun u => placedPoint S p2 .X (e u).2
  let Z := fun u => placedPoint S p2 .Z (e u).1
  have h := avg_orderedIndicator_norm_sq_le_of_not_linear (scalarPolynomial P g)
    (Finset.mem_filter.mp hg).2 X Z (fun _ => placedPoint_projective S p2 .X _)
    (fun _ => placedPoint_projective S p2 .Z _) (polyOutcomeState S p1 R g)
  rw [avgOver_uniform_equiv_prod e, @FieldModel.card P.q P.model.toFieldModel] at h
  have he (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
      scalarBaseQuestionEquiv P (u, v) = fiberQuestionEquiv P .X (e u, v) := rfl
  let f := scalarPolynomial P g
  refine le_trans (b := ((f.support.sup fun e => (f.coeff e).totalDegree) +
    max 1 f.totalDegree + 1 : ℕ) / (P.q : ℝ) * ‖polyOutcomeState S p1 R g‖ ^ 2) ?_ ?_
  · simpa only [fiberAverage, X, Z, scalarPolynomial_eval, he, Equiv.apply_symm_apply,
      fiberImage, PauliKind.other] using h
  · gcongr
    exact_mod_cast (Nat.le_of_add_le_add_right (scalarPolynomial_degree_term_le P g))

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
