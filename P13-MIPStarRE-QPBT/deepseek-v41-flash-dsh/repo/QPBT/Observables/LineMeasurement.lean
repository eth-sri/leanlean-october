module

public import QPBT.Observables.LineMeasurement.LinePointConsistency

/-!
# Expanded line measurements

For a generalized-Pauli basis `W` and a canonical line, the expanded line
measurement is the convolution of the strategy line measurement with the
projective measurement of one Pauli register whose outcome is the restriction
to that line of the low-degree encoding of the measured basis label. This file
states the three consistency conclusions the source draws for that family,
together with the existential form in which the source states them.

The argument runs as follows. Restricting a multilinear low-degree encoding to
a line gives a polynomial of degree at most `m*d` in the line parameter, and at
most `d` on an axis-parallel line (`LineMeasurement.Restriction`), whose
partial evaluation at a sampled point obeys the elementary calculus of
`LineMeasurement.Evaluation`.
Coarse-graining the generalized Pauli basis measurement along that restriction
gives the ancillary projectors `tau^{W,line}`, which are symmetric and hence
perfectly self-consistent on an EPR pair (`LineMeasurement.Projector`). Their
convolution with the strategy line measurement is again projective and vanishes
outside the degree-`d` outcomes on an axis line (`LineMeasurement.Expanded`).
Self-consistency of the convolution follows from self-consistency of the
strategy line measurements and the data-processing inequality
(`LineMeasurement.SelfConsistency`). The overlap of an expanded line
measurement with the expanded point effects selected by evaluation at the
sampled point factorizes exactly through the ancillary consistency of
`tau^{W,line}` with `tau^{W,u}` (`LineMeasurement.LinePointOverlap`); the
generic bipartite estimates of `LineMeasurement.BipartiteTransport` carry that
overlap to the two bipartitions of the six registers, giving the
evaluation-class conclusion (`LineMeasurement.EvalClassConsistency`) and, by
projective refinement, the line-versus-point conclusion
(`LineMeasurement.LinePointConsistency`).

Two features of this route differ from the source. The source derives its third
item from its second; here the evaluation-class estimate comes first, from the
exact overlap identity, and the second item follows from it by projective
refinement, so that the source's elementary sub-measurement inequality is not
needed. The source also transports a relation proved for one pair of register
placements to the remaining three by the symmetry of the test
(`lem:symmetric-equivalents-transfer`, which is not formalized); here each of
the four directed opposite-placement pairs is proved directly. The estimates
established are linear in `ε` for all three items, hence stronger than the
square-root error whenever `ε ≤ 1`; they are weakened to the common error
`deltaLine ε = √ε` only because the source states the three items with a single
error function (`LineMeasurement.SquareRootError`).

## References

The declarations formalize `def:expanded-line-measurement` and
`lem:qld-comm-line-cons` of `blueprint/src/chapter/ch14_qpbt_observables.tex`.
Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:523-678`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

local instance pauliEdgeNonemptyLineMeasurement : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-- The square-root error exhibited by the expanded-line consistency proof.
This is the final quantitative conclusion of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:675-677`. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

/-- Evaluation classes of expanded line measurements are consistent with the
completed expanded point family, including the `none` class. This is item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`, blueprint
`eq:qld-comm-line-pt-cons2`.

The source obtains this item from its second one through an elementary
inequality for projective sub-measurements, which costs a square root. Here the
exact overlap identity of `LineMeasurement.LinePointOverlap` gives a bound
linear in `ε` directly; as for item 2 it is combined with the universal bound
`4` and weakened to the common square-root error of the lemma. -/
theorem exp_line_point_cons_explicit' :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place p₁
          ((S.lineEvalMeasExp p₁.side W sample.1 sample.2).effect a))
        (fun sample a => S.place p₂
          ((S.pointMeasExpOption p₂.side W sample.2).effect a))
        S.psiHat ≤ 348 * deltaLine ε := by
  intro P ε S p₁ p₂ hopp W
  have hε : 0 ≤ ε := S.eps_nonneg
  have key : ∀ (x a : ℝ), 1 ≤ a → a ≤ 86 + 86 → 0 ≤ x → x ≤ 2 * (a * ε) →
      x ≤ 4 → x ≤ 348 * deltaLine ε := by
    intro x a ha haC hx0 hxa hx4
    calc
      x ≤ (2 * a + 4) * Real.sqrt ε :=
        le_mul_sqrt_of_le_mul_of_le_four (by linarith) hx0
          (by rw [mul_assoc]; exact hxa) hx4
      _ ≤ 348 * Real.sqrt ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ε)
        linarith
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  cases p₁ <;> cases p₂ <;> simp [Placement.IsOpposite] at hopp
  · have hb := (ProjectiveSetting.evalClassDist_aaBa_le S W).trans
      (mul_le_mul_of_nonneg_left
        (WinImplications.win_low_degree_explicit P ε S hε W) htwo)
    simpa using key _ 86 (by norm_num) (by norm_num)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_aaBa_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_baAa_le S W).trans
      (mul_le_mul_of_nonneg_left
        (WinImplications.win_low_degree_interchanged_explicit P ε S hε W) htwo)
    simpa using key _ 86 (by norm_num) (by norm_num)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_baAa_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_bbAb_le S W).trans
      (mul_le_mul_of_nonneg_left
        (WinImplications.win_low_degree_interchanged_explicit P ε S hε W) htwo)
    simpa using key _ 86 (by norm_num) (by norm_num)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_bbAb_le_four S W)
  · have hb := (ProjectiveSetting.evalClassDist_abBb_le S W).trans
      (mul_le_mul_of_nonneg_left
        (WinImplications.win_low_degree_explicit P ε S hε W) htwo)
    simpa using key _ 86 (by norm_num) (by norm_num)
      (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (ProjectiveSetting.evalClassDist_abBb_le_four S W)

end

end MIPStarRE.QPBT
