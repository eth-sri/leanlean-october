module

public import QPBT.Combining.OrderedPolynomialEstimates
public import QPBT.Combining.Lines.PairStateConsistencyTransport
public import QPBT.Combining.ExtendedLineGame.PassingValue
public import QPBT.Combining.DirectLowDegree.AnyStrategySoundness
public import QPBT.Games.DistanceTheorems.RoundingTransport
public import QPBT.Combining.RoundedError

/-!
# Rounded extended-polynomial ordered estimates

Direct soundness retains all three consistency conclusions through compression.
Its same-space projective rounding supplies the point comparison used in both
ordered estimates, with the actual point and line errors retained.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1300`.
The directly indexed completed-answer restriction is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ExtendedLineGame

section

variable (P : AdmissibleParams)
include P

/-- Polynomial outcomes and measurements on the extended low-degree carrier. -/
abbrev ExtendedPoly := DirectPolyTuple P.extendedDirectLd

abbrev ExtendedPolyMeas (I : Type*) [Fintype I] [DecidableEq I] :=
  DirectPolyMeasTuple P.extendedDirectLd I

/-- Evaluation of the single extended polynomial returned by direct soundness,
at the point with blocks `(x,z,alpha,beta)`, in the canonical Pauli scalar field.
The singleton tuple carrier is exactly the `k = 1` soundness outcome carrier. -/
def extendedPolynomialRead (x : ExtendedPointQuestion P)
    (g : ExtendedPoly P) : PauliScalar P :=
  extendedDirectScalarEquiv P
    (evalDirectPolyTupleAt ((directPointExtendedQuestionEquiv P).symm x) g (0 : Fin 1))

/-- Undoing the joint coordinate equivalence recovers direct polynomial evaluation. -/
private theorem extendedPolynomialRead_equiv
    (u : DirectPoint P.extendedDirectLd) :
    extendedPolynomialRead P (directPointExtendedQuestionEquiv P u) =
      fun g => extendedDirectScalarEquiv P (evalDirectPolyTupleAt u g (0 : Fin 1)) := by
  funext g
  unfold extendedPolynomialRead
  rw [Equiv.symm_apply_apply]

end

/-- The full polynomial-outcome squared-norm sum in `eq:qld-g-42/43`.
The order parameter selects either `M_X M_Z` or `M_Z M_X`.
The polynomial effect acts on `p1` and both point effects on `p2`. -/
def extendedPolynomialOrderedError {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p1 p2 : Placement)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (W : PauliKind) : ℝ :=
  avgOver (uniformDistribution (ExtendedPointQuestion P)) (fun x =>
    ∑ g, ‖applyOperatorToState (S.place p1 (R.effect g) *
      (1 - S.place p2 (S.extendedPointProduct p2.side W
        x (extendedPolynomialRead P x g)))) S.psiHat‖ ^ 2)

/-- The same rounded projective family satisfies both ordered point comparisons. -/
structure OrderedPolyWitness {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (δ : ℝ) where
  measure : (side : PlayerSide) → ExtendedPolyMeas P (S.ExpandedLocalSpace side)
  projective : ∀ side, Measurement.IsProjective (measure side)
  ordered : ∀ {p : Placement}, p.Primary → ∀ W : PauliKind,
    extendedPolynomialOrderedError S p (ProjectiveSetting.overlapPartner p) (measure p.side) W ≤ δ

/-- Specialize projective refinement to the full polynomial-outcome norm sum. -/
private theorem ordered_error_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : ExtendedPolyMeas P (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (eta : ℝ)
    (hpoint : S.placedDefect p1 p2 (uniformDistribution (ExtendedPointQuestion P))
      (fun x => R.postprocess (extendedPolynomialRead P x)) (points.extendedQ p2.side) ≤ eta)
    (W : PauliKind) :
    extendedPolynomialOrderedError S p1 p2 R W ≤ 4 * eta + 8 * δQ := by
  simpa only [extendedPolynomialOrderedError, mul_sub, mul_one, opFamilyDistSq] using
    points.ordered_dist_le p1 p2 hopposite R hR (extendedPolynomialRead P)
      eta hpoint W

/-- Reading the single scalar of an actual direct-game point answer recovers `Q`. -/
private theorem point_scalar_measurement {P : AdmissibleParams} {ε δQ δL : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : ExtendedLinesWitness S points δL) (side : PlayerSide)
    (u : DirectPoint P.extendedDirectLd) :
    (((answerMeasurement lines side (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (directLdPointValuesOrZero P.extendedDirectLd)).postprocess
        (fun values => extendedDirectScalarEquiv P (values (0 : Fin 1)))) =
      points.extendedQ side (directPointExtendedQuestionEquiv P u) := by
  rw [directPointExtendedQuestionEquiv_apply]
  simp only [answerMeasurement, directLdPointQuestionOf,
    MIPStarRE.Quantum.Measurement.postprocess_comp,
    pointAnswer, directLdPointValuesOrZero, RingEquiv.apply_symm_apply]
  apply MIPStarRE.Quantum.Measurement.ext
  intro a
  change (∑ b ∈ Finset.univ.filter (fun b : PauliScalar P => b = a), _) = _
  simp_all [Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, if_true]

set_option maxHeartbeats 800000 in
/-- Round concrete polynomial measurements satisfying the three direct
soundness bounds and transport them to the two ordered point comparisons. -/
private theorem rounded_polynomial_ordered_estimates_of_soundness
    {P : AdmissibleParams} {ε δQ δL : ℝ} (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ) (lines : ExtendedLinesWitness S points δL)
    (delta : ℝ)
    (A : ExtendedPolyMeas P (S.ExpandedLocalSpace .alice))
    (B : ExtendedPolyMeas P (S.ExpandedLocalSpace .bob))
    (h : DirectLdConsistency (strategy lines) A B delta delta)
    (hdelta : 0 ≤ delta) :
    Nonempty (OrderedPolyWitness S (4 * roundedLdError delta + 8 * δQ)) := by
  classical
  let eta := roundedLdError delta
  obtain ⟨hB, hA, hAB⟩ := h
  obtain ⟨RA, RB, hRA, hRB, _, _, htransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency
      (pairState S) (pairState_norm S) A B delta hdelta hAB
  have hround := htransport
    (uniformDistribution (DirectPoint P.extendedDirectLd))
    (uniformDistribution_isProbability _) (fun u => evalDirectPolyTupleAt u)
  have hRApoint := hround.1
    (directLdPointReadout (strategy lines).B) delta hA
  have hRBpoint := hround.2
    (directLdPointReadout (strategy lines).A) delta hB
  rw [← two_mul delta] at hRApoint hRBpoint
  change consistencyDefect _ _ _ _ ≤ eta at hRApoint hRBpoint
  have hAscalar := (consistencyDefect_postprocess_question_le
    (uniformDistribution (DirectPoint P.extendedDirectLd))
    (fun u => RA.postprocess (evalDirectPolyTupleAt u))
    (directLdPointReadout (strategy lines).B) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRApoint
  have hBscalar := (consistencyDefect_postprocess_question_le
    (uniformDistribution (DirectPoint P.extendedDirectLd))
    (directLdPointReadout (strategy lines).A)
    (fun u => RB.postprocess (evalDirectPolyTupleAt u)) (pairState S)
    (fun _ values => extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRBpoint
  change consistencyDefect _ _ _ (pairState S) ≤ eta at hAscalar hBscalar
  dsimp only [strategy, directLdPointReadout] at hAscalar hBscalar
  conv at hAscalar =>
    lhs; arg 3; ext u c; arg 2; arg 1
    erw [point_scalar_measurement lines .bob u]
  conv at hBscalar =>
    lhs; arg 2; ext u c; arg 1; arg 1
    erw [point_scalar_measurement lines .alice u]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_comp] at hAscalar hBscalar
  conv at hAscalar =>
    lhs; arg 2; ext u c; arg 1; arg 1
    rw [← extendedPolynomialRead_equiv P u]
  conv at hBscalar =>
    lhs; arg 3; ext u c; arg 2; arg 1
    rw [← extendedPolynomialRead_equiv P u]
  have hAquestion : bipartiteDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x => RA.postprocess (extendedPolynomialRead P x))
      (points.extendedQ .bob) (pairState S) ≤ eta := by
    rw [bipartiteDefect, ← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    exact hAscalar
  have hBquestion : bipartiteDefect (uniformDistribution (ExtendedPointQuestion P))
      (points.extendedQ .alice)
      (fun x => RB.postprocess (extendedPolynomialRead P x))
      (pairState S) ≤ eta := by
    rw [bipartiteDefect, ← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    exact hBscalar
  have hAplaced := (S.consistencyDefect_pairState_eq_AA'_BA'' _ _ _).symm.trans_le hAquestion
  have hBplaced := (S.consistencyDefect_pairState_eq_BB'_AB'' _ _ _).symm.trans_le hBquestion
  let R : (side : PlayerSide) → ExtendedPolyMeas P (S.ExpandedLocalSpace side)
    | .alice => RA
    | .bob => RB
  have hR (side) : Measurement.IsProjective (R side) := by
    cases side
    · exact hRA
    · exact hRB
  refine ⟨R, hR, ?_⟩
  intro p hp W
  refine ordered_error_le points p _ p.opposite_partner (R p.side) (hR _) eta ?_ W
  cases hp
  · exact hAplaced
  · exact hBplaced

set_option maxHeartbeats 800000 in
-- The proof elaborates both ordered finite-sum estimates and their rounded witnesses.
/-- Direct soundness and same-space rounding construct extended-polynomial
projective measurements satisfying both ordered estimates on `AA'|BA''` and
`BB'|AB''`. The actual passing error is
`3 * (sqrt (deltaQ + deltaL) + m*d/q)`. All three compressed soundness
conclusions are used; in particular the polynomial consistency error is `delta`,
not the weaker point-derived estimate. The rounded point error is
`eta = delta + sqrt (220 * delta^(1/4)) + 2 * sqrt (2 * delta)`.

This proves the calculation `eq:qld-g-42/43` from the directly indexed extended
line witness with its completed-answer domain. It does not construct that line
witness, prove polynomial separation, or certify source lemma `lem:qld-4-7`.
The remaining source obligations are tracked by issues #515 and #598 and the
module's paper-gap references. -/
theorem rounded_polynomial_ordered_estimates_explicit :
    ∀ (P : AdmissibleParams) (ε δQ δL : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ) (_lines : ExtendedLinesWitness S points δL),
      let delta := P.extendedLdError pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower δQ δL
      Nonempty (OrderedPolyWitness S (4 * roundedLdError delta + 8 * δQ)) := by
  classical
  let a := pauliBaselineLowDegreeConstant
  have ha : 1 ≤ a := by
    dsimp only [a, pauliBaselineLowDegreeConstant]
    norm_num
  intro P ε δQ δL S points lines delta
  have hm := P.one_le_m
  have hd := P.hd
  have hq : 0 < P.q := by
    obtain ⟨k, _, hk⟩ := P.hq
    rw [hk]
    positivity
  have hpos : 0 < directPassingErrorEnvelope (δQ + δL) P.degreeRatio :=
    directPassingErrorEnvelope_pos _ _ (by positivity)
  obtain ⟨A, B, h⟩ :=
    direct_ld_soundness_of_k_eq_one_any_strategy_explicit P.extendedDirectLd _ rfl hpos
      (strategy lines) (by simpa only [AdmissibleParams.degreeRatio, AdmissibleParams.degreeBudget,
        Nat.cast_mul] using strategy_value_ge_directPassingErrorEnvelope lines)
  have hdelta : 0 ≤ delta := by
    dsimp [delta, AdmissibleParams.extendedLdError, deltaLd]
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    positivity
  exact rounded_polynomial_ordered_estimates_of_soundness
    S points lines delta A B h hdelta

end ExtendedLineGame

end

end MIPStarRE.QPBT
