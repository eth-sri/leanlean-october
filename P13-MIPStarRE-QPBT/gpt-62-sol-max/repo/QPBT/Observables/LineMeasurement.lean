module

public import QPBT.Observables.PlacementSupport
public import QPBT.Observables.LineMeasurement.BipartiteTransport

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
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- The square-root error exhibited by the expanded-line consistency proof.
This is the final quantitative conclusion of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:675-677`. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 400 in
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
  classical
  obtain rfl := Placement.eq_overlapPartner hopp
  let μ := linePointDist P.toLdParams
  let q := ProjectiveSetting.overlapPartner p₁
  let A := fun x : LinePointSample P.toLdParams =>
    S.placedMeasurement p₁ (S.lineEvalMeasExp p₁.side W x.1 x.2)
  let B := fun x : LinePointSample P.toLdParams =>
    S.placedMeasurement q (S.pointMeasExpOption q.side W x.2)
  have hμ := linePointDist_isProbability P.toLdParams
  have h := opFamilyDistSq_le_two_mul_consistencyDefect μ A B S.psiHat
  rw [consistencyDefect_eq_one_sub_overlap μ A B S.psiHat hμ S.psiHat_norm] at h
  simp only [A, B, q, ProjectiveSetting.placedMeasurement_effect] at h
  simp_rw [S.sum_stateQForm_evalClass_placement_eq] at h
  let ov := fun x : LinePointSample P.toLdParams =>
    ∑ a, S.strategyOverlap p₁ ((S.lineEvalMeas p₁.side W x.1 x.2).effect a)
      ((S.pointMeasOption q.side W x.2).effect a)
  change _ ≤ 2 * (1 - avgOver μ ov) at h
  have hw : 1 - avgOver μ ov ≤ 86 * ε := by
    have hA := WinImplications.win_low_degree_explicit P ε S S.eps_nonneg W
    have hB := WinImplications.win_low_degree_interchanged_explicit P ε S S.eps_nonneg W
    rw [consistencyDefect_placed_eq_one_sub_overlap μ
      (fun x => S.lineEvalMeas .alice W x.1 x.2) (fun x => S.pointMeasOption .bob W x.2)
      _ hμ S.toStrategy.ψ_norm] at hA
    rw [consistencyDefect_placed_eq_one_sub_overlap μ
      (fun x => S.pointMeasOption .alice W x.2) (fun x => S.lineEvalMeas .bob W x.1 x.2)
      _ hμ S.toStrategy.ψ_norm] at hB
    cases p₁
    case AA' | AB'' => exact hA
    case BA'' | BB' => exact hB
  have hpos : 0 ≤ avgOver μ ov := by
    unfold ov
    apply avgOver_nonneg
    intro x
    refine Finset.sum_nonneg fun a _ => ?_
    cases p₁
    case AA' | AB'' =>
      exact stateQForm_nonneg _ (kronecker_nonneg ((S.lineEvalMeas .alice W x.1 x.2).pos a)
        ((S.pointMeasOption .bob W x.2).pos a))
    case BA'' | BB' =>
      exact stateQForm_nonneg _ (kronecker_nonneg ((S.pointMeasOption .alice W x.2).pos a)
        ((S.lineEvalMeas .bob W x.1 x.2).pos a))
  change measurementDistSq μ A B S.psiHat ≤ _
  have hlin := h.trans (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 2))
  have hfour := h.trans (show 2 * (1 - avgOver μ ov) ≤ 4 by linarith)
  rw [show 2 * (86 * ε) = 172 * ε by ring] at hlin
  have hs := le_mul_sqrt_of_le_mul_of_le_four (by norm_num : (1 : ℝ) ≤ 172)
    (opFamilyDistSq_nonneg μ _ _ _) hlin hfour
  change _ ≤ 348 * Real.sqrt ε
  exact hs.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ε))

end

end MIPStarRE.QPBT
