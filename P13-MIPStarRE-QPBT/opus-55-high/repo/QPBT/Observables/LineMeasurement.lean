module

public import QPBT.Observables.LineMeasurement.EvalClassConsistency

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
  have key : ∀ {x y : ℝ}, y ≤ 86 * ε → 0 ≤ x → x ≤ min (2 * y) 4 → x ≤ 348 * deltaLine ε :=
    fun {x y} hy hx0 hx => (le_mul_sqrt_of_le_mul_of_le_four (ε := ε) (a := 344) (by norm_num) hx0
      (by linarith [min_le_left (2 * y) 4, S.eps_nonneg]) (hx.trans (min_le_right _ _))).trans_eq
        (by norm_num [deltaLine])
  have hμ := linePointDist_isProbability P.toLdParams
  have h1 := WinImplications.win_low_degree_explicit P ε S S.eps_nonneg W
  have h2 := WinImplications.win_low_degree_interchanged_explicit P ε S S.eps_nonneg W
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · refine key h1 (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) ?_
    simp only [opFamilyDistSq, ProjectiveSetting.norm_place_AA'_sub_place_BA'']
    exact DistanceCalculus.opFamilyDistSq_placed_le_min _ hμ (fun x => S.lineEvalMeasExp .alice W x.1 x.2)
      (fun x => DistanceCalculus.leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
        (S.pointMeasExpOption .bob W x.2)) _ (S.norm_reindexState_psiHat _) (fun x => S.lineEvalMeas .alice W x.1 x.2)
      (fun x => S.pointMeasOption .bob W x.2) _ S.toStrategy.ψ_norm fun x =>
        (Finset.sum_congr rfl fun a _ => S.stateQForm_aaBa_mul_eq _ _).trans (S.sum_stateQForm_evalClass_AA'_BA''_eq W x.1 x.2)
  · refine key h2 (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) ?_
    rw [DistanceCalculus.opFamilyDistSq_symm]; simp only [opFamilyDistSq, ProjectiveSetting.norm_place_AA'_sub_place_BA'']
    exact DistanceCalculus.opFamilyDistSq_placed_le_min _ hμ (fun x => S.pointMeasExpOption .alice W x.2)
      (fun x => DistanceCalculus.leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
        (S.lineEvalMeasExp .bob W x.1 x.2)) _ (S.norm_reindexState_psiHat _) (fun x => S.pointMeasOption .alice W x.2)
      (fun x => S.lineEvalMeas .bob W x.1 x.2) _ S.toStrategy.ψ_norm fun x =>
        (Finset.sum_congr rfl fun a _ => S.stateQForm_aaBa_mul_eq _ _).trans (S.sum_stateQForm_evalClass_BA''_AA'_eq W x.1 x.2)
  · refine key h2 (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) ?_
    rw [DistanceCalculus.opFamilyDistSq_symm]; simp only [opFamilyDistSq, ProjectiveSetting.norm_place_AB''_sub_place_BB']
    exact DistanceCalculus.opFamilyDistSq_placed_le_min _ hμ (fun x => S.pointMeasExpOption .alice W x.2)
      (fun x => DistanceCalculus.leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
        (S.lineEvalMeasExp .bob W x.1 x.2)) _ (S.norm_reindexState_psiHat _) (fun x => S.pointMeasOption .alice W x.2)
      (fun x => S.lineEvalMeas .bob W x.1 x.2) _ S.toStrategy.ψ_norm fun x =>
        (Finset.sum_congr rfl fun a _ => S.stateQForm_abBb_mul_eq _ _).trans (S.sum_stateQForm_evalClass_BB'_AB''_eq W x.1 x.2)
  · refine key h1 (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) ?_
    simp only [opFamilyDistSq, ProjectiveSetting.norm_place_AB''_sub_place_BB']
    exact DistanceCalculus.opFamilyDistSq_placed_le_min _ hμ (fun x => S.lineEvalMeasExp .alice W x.1 x.2)
      (fun x => DistanceCalculus.leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
        (S.pointMeasExpOption .bob W x.2)) _ (S.norm_reindexState_psiHat _) (fun x => S.lineEvalMeas .alice W x.1 x.2)
      (fun x => S.pointMeasOption .bob W x.2) _ S.toStrategy.ψ_norm fun x =>
        (Finset.sum_congr rfl fun a _ => S.stateQForm_abBb_mul_eq _ _).trans (S.sum_stateQForm_evalClass_AB''_BB'_eq W x.1 x.2)

end

end MIPStarRE.QPBT
