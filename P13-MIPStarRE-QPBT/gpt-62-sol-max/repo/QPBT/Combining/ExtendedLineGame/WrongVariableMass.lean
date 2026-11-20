module

public import QPBT.Combining.ExtendedLineGame.ScalarNonlinearMass
public import QPBT.Combining.PolynomialFiberBounds

/-!
# Wrong-variable mass of rounded polynomial outcomes

The two block orders use the actual projected state vectors and the full
ordered-error sum. A common exceptional coefficient controls all outcomes
of the fixed-block measurement before their weights are summed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1368`,
`eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, and the two wrong-variable
mass bounds. This supports blueprint `lem:qld-4-7`; it does not establish
the subsequent retained overlaps or global polynomial-pair witness.
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

section

variable (p : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p.side))

/-- Actual mass of scalar-linear outcomes whose second coefficient in the
chosen order depends on the varying block. In order `XZ` this is the coefficient
of beta depending on x; in order `ZX` it is the coefficient of alpha depending
on z. These are the two classes in `eq:qld-g-prime-xpt-bound` and
`eq:qld-g-prime-zpt-bound`, supporting blueprint `lem:qld-4-7`. -/
def scalarWrongVariableMass
    (W : PauliKind) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g =>
    ScalarLinear P g ∧ ¬ ScalarBlockConstant P g W),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

/-- Both wrong-variable classes are bounded in their appropriate actual
ordered errors, for every pair of opposite placements. The common exceptional
coefficient and both `md` degree bounds are derived internally. Completeness
and normalization retain the full outcome sum, so there is no outcome-count
loss. This is the quantitative concentration step of
`eq:qld-g-prime-xpt-bound` and `eq:qld-g-prime-zpt-bound`, supporting
blueprint `lem:qld-4-7`. -/
theorem scalarWrongVariableMass_le_ordered_error (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (W : PauliKind) :
    scalarWrongVariableMass S p1 R W ≤
      2 * extendedPolynomialOrderedError S p1 p2 R W +
        2 * (((P.m * P.d + P.m * P.d + 2 : ℕ) : ℝ) / P.q) := by
  classical
  let s := Finset.univ.filter (fun g =>
    ScalarLinear P g ∧ ¬ ScalarBlockConstant P g W)
  let X := placedPoint S p2 W
  let Z := placedPoint S p2 W.other
  refine polyOutcomeMass_le_orderedError S p1 p2 hopposite R hR W s _ (by positivity) ?_
  intro g hg
  obtain ⟨hlin, hnon⟩ := (Finset.mem_filter.mp hg).2
  have hd := blockCoefficientPolynomial_degrees P g
    (Finsupp.single (W.component (1, 0)) 1) W
  have h := avg_orderedIndicator_norm_sq_le_of_nonconstant
    (blockCoefficientPolynomial P g (Finsupp.single (W.component (1, 0)) 1) W)
    hnon hd.1 hd.2
    (fun x z => MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
      (blockCoefficientPolynomial P g
        (Finsupp.single (W.component (0, 1)) 1) W))) X Z
    (placedPoint_projective S p2 _)
    (placedPoint_projective S p2 _) (polyOutcomeState S p1 R g)
  have hcard :=
    @FieldModel.card P.q P.model.toFieldModel
  simpa only [fiberAverage, fiberImage, scalarPolynomial_linear_read_fiber P g hlin, hcard] using h

/-- Mass outside the existing bounded polynomial-pair combining image after
the canonical field transport. This is the actual separated image of
`eq:qld-g-non-separable` and `def:combine-map`, supporting blueprint
`lem:qld-4-7`; no completion or overlap assertion is included. -/
def separatedPolynomialMass : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g => g ∉ Set.range (directCombinedEmbedding P)),
    ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2

private theorem separatedPolynomialMass_le_three_masses :
    separatedPolynomialMass S p R ≤ scalarNonlinearMass S p R +
      scalarWrongVariableMass S p R .X + scalarWrongVariableMass S p R .Z := by
  classical
  simp only [separatedPolynomialMass, scalarNonlinearMass, scalarWrongVariableMass,
    Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have h := sq_nonneg ‖applyOperatorToState (S.place p (R.effect g)) S.psiHat‖
  by_cases hlin : ScalarLinear P g <;> by_cases hX : ScalarBlockConstant P g .Z <;>
    by_cases hZ : ScalarBlockConstant P g .X
  · simp [hlin, hX, hZ, scalarSeparated_mem_range P g hlin hX hZ]
  all_goals simp [hlin, hX, hZ] <;> split_ifs <;> linarith

end

/-- The union of the three excluded classes is bounded in the actual two
ordered errors. The image is the existing faithful `combinePoly` encoding
with both components in `Poly P`. This proves concentration only, as in
`eq:qld-g-non-separable`, supporting blueprint `lem:qld-4-7`. -/
theorem separatedPolynomialMass_le_ordered_errors (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) :
    separatedPolynomialMass S p1 R ≤
      4 * extendedPolynomialOrderedError S p1 p2 R .X +
      2 * extendedPolynomialOrderedError S p1 p2 R .Z +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  have h := separatedPolynomialMass_le_three_masses S p1 R
  have hN := scalarNonlinearMass_le_ordered_error S p1 p2 hopposite R hR
  have hX := scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR .Z
  have hZ := scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR .X
  refine h.trans ((add_le_add (add_le_add hN hZ) hX).trans_eq ?_)
  push_cast
  ring

end

/-- Both actual rounded measurements concentrate on faithful separated
polynomial pairs, with error `6E + (12md + 4d + 10)/q` and
`E = 4eta + 8deltaQ`. The same measurements retain both ordered estimates.
The point and directly indexed completed-answer line witnesses are precisely
the inputs of the preceding rounded constructor, with the same documented
domain restriction. This proves `eq:qld-g-non-separable`, supporting
blueprint `lem:qld-4-7`, without claiming the subsequent retained overlaps
or the source global-pair witness. -/
theorem rounded_polynomial_separated_mass_explicit :
    ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := P.extendedLdError pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower δQ δL
      let eta := roundedLdError delta
      ∃ w : OrderedPolyWitness S (4 * eta + 8 * δQ),
        ∀ {p : Placement}, p.Primary → separatedPolynomialMass S p (w.measure p.side) ≤
          6 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  intro P ε δQ δL S points lines delta eta
  obtain ⟨w⟩ := rounded_polynomial_ordered_estimates_explicit P ε δQ δL S points lines
  refine ⟨w, ?_⟩
  intro p hp
  have h := separatedPolynomialMass_le_ordered_errors S p _ p.opposite_partner
    (w.measure p.side) (w.projective p.side)
  linarith [w.ordered hp .X, w.ordered hp .Z]

end ExtendedLineGame

end

end MIPStarRE.QPBT
