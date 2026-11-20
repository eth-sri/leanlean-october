module

public import QPBT.Combining.Lines.Conditioning
public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.PassingError
public import QPBT.Combining.DirectLowDegree.Transport.Error
public import QPBT.ExplicitConstants
public import QPBT.Games.Sandwich.Pasting.Heterogeneous

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

section

variable {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error)
    (first second : Placement)
include params error setting first second

set_option synthInstance.maxSize 400 in
/-- Every directed opposite placement has an actual heterogeneous
bipartition. The unused EPR pair is included on the right. This discharges the
register identities needed for the application of pasting in all symmetric
equivalents of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:959-963`. -/
theorem ProjectiveSetting.exists_opposite_bipartition (hopposite : first.IsOpposite second) :
    ∃ equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
        setting.ExpandedLocalSpace first.side ×
          (setting.ExpandedLocalSpace second.side ×
            (PauliRegister params × PauliRegister params)),
      (∀ operator : Op (setting.ExpandedLocalSpace first.side),
        reindexOp equivalence (heteroKron operator 1) = setting.place first operator) ∧
      (∀ operator : Op (setting.ExpandedLocalSpace second.side),
        reindexOp equivalence (heteroKron 1 (heteroKron operator
          (1 : Op (PauliRegister params × PauliRegister params)))) =
          setting.place second operator) := by
  obtain rfl := Placement.eq_overlapPartner hopposite
  exact ⟨setting.placeSplit first, fun O => (setting.place_eq_reindex first O).symm,
    setting.reindexOp_placeSplit_partner first⟩

set_option synthInstance.maxSize 400 in
open DistanceCalculus in
/-- Coordinate transport of arbitrary placed operator families through a
specified opposite bipartition. The two identities are representation data,
constructed for every opposite pair by `exists_opposite_bipartition`; no
mathematical approximation or extra assumption on the strategy is introduced. -/
theorem ProjectiveSetting.consistencyDefect_bipartition
    (equivalence : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
      setting.ExpandedLocalSpace first.side ×
        (setting.ExpandedLocalSpace second.side × (PauliRegister params × PauliRegister params)))
    (hfirst : ∀ operator : Op (setting.ExpandedLocalSpace first.side),
      reindexOp equivalence (heteroKron operator 1) = setting.place first operator)
    (hsecond : ∀ operator : Op (setting.ExpandedLocalSpace second.side),
      reindexOp equivalence (heteroKron 1 (heteroKron operator
        (1 : Op (PauliRegister params × PauliRegister params)))) =
        setting.place second operator)
    {question answer : Type*} [Fintype question] [DecidableEq question]
    [Fintype answer] [DecidableEq answer] (law : Distribution question)
    (firstFamily : question → answer → Op (setting.ExpandedLocalSpace first.side))
    (secondFamily : question → answer → Op (setting.ExpandedLocalSpace second.side)) :
    consistencyDefect law (fun query output => heteroKron (firstFamily query output) 1)
      (fun query output => heteroKron 1 (heteroKron (secondFamily query output)
        (1 : Op (PauliRegister params × PauliRegister params))))
      (reindexState equivalence setting.psiHat) =
    consistencyDefect law (fun query output => setting.place first (firstFamily query output))
      (fun query output => setting.place second (secondFamily query output)) setting.psiHat := by
  unfold consistencyDefect
  congr 1
  funext query
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro other _
  split_ifs
  · rfl
  · rw [DistanceCalculus.stateQForm_reindexState, reindexOp_mul,
      hfirst, hsecond]

end

/-- Placing both input measurements leaves the unused tensor register untouched. -/
private theorem pastedPOVM_leftPlaced {A B I J : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : Quantum.Measurement A I) (Q : Quantum.Measurement B I) (hQ : QPBT.Measurement.IsProjective Q) :
    pastedPOVM (leftPlacedMeasurement (ιB := J) P) (leftPlacedMeasurement Q)
      (QPBT.Measurement.isProjective_leftPlacement _ hQ) =
        leftPlacedMeasurement (pastedPOVM P Q hQ) := by
  apply Quantum.Measurement.ext
  intro a
  simp only [pastedPOVM, Quantum.Measurement.ofSumEqOne, leftPlacedMeasurement_effect,
    pastedMeasurement, heteroKron_mul, mul_one]

/-- Reversing a paired postprocessing reverses the effect's answer index.
This formalization identity is valid without an injectivity assumption on the
evaluation functions, including completed evaluation at a degenerate line. -/
theorem postprocess_pair_swap_effect {answer first second carrier : Type*}
    [Fintype answer] [DecidableEq answer] [Fintype first] [DecidableEq first]
    [Fintype second] [DecidableEq second] [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement answer carrier) (evaluate : answer → first × second)
    (output : second × first) :
    (measurement.postprocess (fun answer => (evaluate answer).swap)).effect output =
      (measurement.postprocess evaluate).effect output.swap := by
  simp only [Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  simp [Prod.ext_iff, and_comm]

/-- Evaluating the actual X-outer paired-line POVM in Z-then-X answer order
gives precisely the evaluated sandwich in the one-sided pasting conclusion.
This is an identity for all descriptors and points, not only on the support
of the conditioned law. Source: `eq:qld-4-13-1`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem ProjectiveSetting.combinedLineMeasurement_evaluated_eq_pasted
    {params : AdmissibleParams} {error : ℝ} (setting : ProjectiveSetting params error)
    (side : PlayerSide) (lineX lineZ : LineDesc params.toLdParams)
    (pointX pointZ : PauliPoint params) :
    (setting.combinedLineMeasurement side lineX lineZ).postprocess
      (fun polys => (evalOpt lineZ pointZ polys.2, evalOpt lineX pointX polys.1)) =
    (pastedPOVM (setting.lineMeasExp side .Z lineZ) (setting.lineMeasExp side .X lineX)
      (setting.lineMeasExp_isProjective side .X lineX)).postprocess
        (fun polys => (evalOpt lineZ pointZ polys.1, evalOpt lineX pointX polys.2)) := by
  let G := pastedPOVM (setting.lineMeasExp side .Z lineZ) (setting.lineMeasExp side .X lineX)
    (setting.lineMeasExp_isProjective side .X lineX)
  have h : setting.combinedLineMeasurement side lineX lineZ = G.postprocess Prod.swap := by
    apply Quantum.Measurement.ext
    intro a
    exact (SandwichProduct.postprocess_effect_of_injective G Prod.swap Prod.swap_injective a.swap).symm
  rw [h, Quantum.Measurement.postprocess_comp]
  rfl

section

variable (params : AdmissibleParams) (error pointError : ℝ)
    (setting : ProjectiveSetting params error)
    (points : CombinedPointsWitness setting pointError)
    (first second : Placement) (hopposite : first.IsOpposite second)
include params error pointError setting points first second hopposite

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Heterogeneous pasting elaborates nested postprocesses with dependent measurement types.
/-- Applying heterogeneous one-sided pasting to the actual completed point
and line families bounds their conditional defect. Both supplied point
families and both marginal errors are retained. Answers are ordered Z then X,
as required by the X-outer sandwich. Source: `eq:qld-4-13-1`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; the formalization-only conditioning
and point-error dependence are explained in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem combined_line_conditioned_defect_le_explicit :
          setting.placedDefect first second
            (nondegenerateLinePastingDist params.toLdParams) (fun query => (points.Q first.side query.2.2 query.1.2.2).postprocess
                (fun pair => (some pair.2, some pair.1))) (fun query => (setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
                (fun polys => (evalOpt query.1.1.2 query.1.2.2 polys.2,
                  evalOpt query.1.1.1 query.2.2 polys.1))) ≤
            heterogeneousPastingError ((params.m * params.d : ℕ) /
              (Fintype.card (ScalarQ params.toLdParams) : ℝ))
              ((8 * pointError + 2080 * (error + deltaLine error)) /
                nondegenerateLinePastingMass params.toLdParams) := by
  classical
  obtain ⟨equivalence, hfirst, hsecond⟩ :=
    setting.exists_opposite_bipartition first second hopposite
  have hpoint : 0 ≤ pointError :=
    (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _).trans
      (points.self_consistent first second hopposite)
  have hmass := (prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  have hextra : 0 ≤ 2080 * (error + deltaLine error) :=
    mul_nonneg (by norm_num) (add_nonneg setting.eps_nonneg (Real.sqrt_nonneg _))
  have herror : 0 ≤ (8 * pointError + 2080 * (error + deltaLine error)) /
      nondegenerateLinePastingMass params.toLdParams :=
    div_nonneg (by linarith) hmass
  have hbound := pasting_error_heterogeneous_explicit
    (nondegenerateLinePastingDist params.toLdParams)
    (fun (poly : PauliLinePoly params) sample =>
      evalOpt sample.1 sample.2 poly)
    (fun (poly : PauliLinePoly params) sample =>
      evalOpt sample.1 sample.2 poly)
    (fun pair => DistanceCalculus.leftPlacedMeasurement
      (ιB := PauliRegister params × PauliRegister params)
      (setting.lineMeasExp second.side .Z pair.2))
    (fun pair => DistanceCalculus.leftPlacedMeasurement
      (ιB := PauliRegister params × PauliRegister params)
      (setting.lineMeasExp second.side .X pair.1))
    (fun query => (points.Q first.side query.2.2 query.1.2.2).postprocess
      (fun pair => (some pair.2, some pair.1)))
    (reindexState equivalence setting.psiHat)
    ((params.m * params.d : ℕ) / (Fintype.card (ScalarQ params.toLdParams) : ℝ))
    ((8 * pointError + 2080 * (error + deltaLine error)) /
      nondegenerateLinePastingMass params.toLdParams)
    (nondegenerateLinePastingDist_isProbability params.toLdParams)
    (by rw [reindexState_norm_eq, setting.psiHat_norm]) (by positivity) herror
    (fun pair => MIPStarRE.QPBT.Measurement.isProjective_leftPlacement _
      (setting.lineMeasExp_isProjective second.side .X pair.1))
    (fun query => SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _)
    (nondegenerateLinePastingDist_collision_bound params (params.m * params.d))
  have hpaste (x z : LineDesc params.toLdParams) :=
    pastedPOVM_leftPlaced (J := PauliRegister params × PauliRegister params)
      (setting.lineMeasExp second.side .Z z) (setting.lineMeasExp second.side .X x)
      (setting.lineMeasExp_isProjective second.side .X x)
  simp only [bipartiteDefect, pastedEvaluation, hpaste,
    leftPlacedMeasurement_postprocess_effect,
    setting.consistencyDefect_bipartition first second equivalence hfirst hsecond] at hbound
  have hmarginal := combined_points_conditioned_line_marginal_defect_le_explicit
    params error pointError setting points first second hopposite
  simp only [ProjectiveSetting.placedDefect, measurementDefect, consistencyDefect, nondegenerateLinePastingDist,
    Distribution.avgOver_map, ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.lineEvalMeasExp] at hbound hmarginal ⊢
  simpa only [setting.combinedLineMeasurement_evaluated_eq_pasted, heterogeneousPastingError] using
    hbound hmarginal.1 hmarginal.2

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Restoring the discarded directions expands the pasted family and its mass estimate.
/-- The actual X-outer line POVM and the supplied points satisfy the restored
source-law bound. Only zero X directions are discarded during the proof;
their contribution is restored as `1/(2q)`, and the retained mass multiplies
the pasting error. Source: `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; see
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem combined_line_restored_defect_le_explicit :
    setting.placedDefect first second (sourceLinePointPairDist params)
      (fun z => points.completedPair first.side z.1.2 z.2.2)
      (pairedLineReadout (setting.combinedLineMeasurement second.side)) ≤
            nondegenerateLinePastingMass params.toLdParams *
              heterogeneousPastingError ((params.m * params.d : ℕ) /
                (Fintype.card (ScalarQ params.toLdParams) : ℝ))
                ((8 * pointError + 2080 * (error + deltaLine error)) /
                  nondegenerateLinePastingMass params.toLdParams) +
              1 / (2 * Fintype.card (ScalarQ params.toLdParams)) := by
  classical
  have hbound := combined_line_conditioned_defect_le_explicit
    params error pointError setting points first second hopposite
  have hswapPoints (side : PlayerSide) (pointX pointZ : PauliPoint params)
      (output : Option (PauliScalar params) × Option (PauliScalar params)) :
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).effect output =
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output.swap :=
    postprocess_pair_swap_effect (points.Q side pointX pointZ)
      (fun pair : PauliScalar params × PauliScalar params => (some pair.1, some pair.2)) output
  have hswapLines (side : PlayerSide) (lineX lineZ : LineDesc params.toLdParams)
      (pointX pointZ : PauliPoint params)
      (output : Option (PauliScalar params) × Option (PauliScalar params)) :
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (evalOpt lineZ pointZ polys.2, evalOpt lineX pointX polys.1))).effect
          output =
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (evalOpt lineX pointX polys.1, evalOpt lineZ pointZ polys.2))).effect
          output.swap :=
    postprocess_pair_swap_effect (setting.combinedLineMeasurement side lineX lineZ)
      (fun polys => (evalOpt lineX pointX polys.1, evalOpt lineZ pointZ polys.2)) output
  simp_rw [ProjectiveSetting.placedDefect, measurementDefect, ProjectiveSetting.placedMeasurement_effect, hswapPoints, hswapLines] at hbound
  have hswap := consistencyDefect_outcome_equiv
    (nondegenerateLinePastingDist params.toLdParams)
    (Equiv.prodComm (Option (PauliScalar params)) (Option (PauliScalar params)))
    (fun query output => setting.place first
      (((points.Q first.side query.2.2 query.1.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output))
    (fun query output => setting.place second
      (((setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
        (fun polys => (evalOpt query.1.1.1 query.2.2 polys.1,
          evalOpt query.1.1.2 query.1.2.2 polys.2))).effect output)) setting.psiHat
  have hnatural := hswap.symm.trans_le hbound
  refine (setting.combinedLineMeasurement_consistency_le_conditioned
    points first second hopposite).trans ?_
  unfold ProjectiveSetting.placedDefect measurementDefect
  unfold consistencyDefect nondegenerateLinePastingDist at hnatural ⊢
  simp only [Distribution.avgOver_map] at hnatural ⊢
  have hmass : 0 ≤ nondegenerateLinePastingMass params.toLdParams :=
    (prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  exact add_le_add (mul_le_mul_of_nonneg_left hnatural hmass) le_rfl

end

/-- Formalization-only consistency theorem for the particular X-Z-X measurement
constructed in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-961`.

The point family is supplied with its polynomial error bound. The line error
may depend on this function, as in `exists_combinedLinesWitness_ofPointsWitness`.
The conclusion concerns `combinedLineMeasurement` itself, so subsequent uses of
Claim 17-2 retain the source construction.

The point-to-line comparisons and pasting argument at paper lines 900--961
prove this estimate. Conditioning excludes only zero X directions; their
probability is bounded and restored in the original law. See
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`; no equality or marginal
assumption is added to a paper-facing theorem. -/
theorem combined_line_measurement_consistency (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε))
        (p1 p2 : Placement), p1.IsOpposite p2 →
        S.placedDefect p1 p2 (sourceLinePointPairDist P)
          (pairedLineReadout (S.combinedLineMeasurement p1.side))
          (fun s => points.completedPair p2.side s.1.2 s.2.2) ≤
          deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) := by
  classical
  obtain ⟨lineError, hlineError, hscalar⟩ := exists_conditioned_polynomial_bound
    deltaQ hdeltaQ 2080 (by norm_num) heterogeneousPastingError heterogeneous_pasting_error_is_poly_err₂
  refine ⟨lineError, hlineError, ?_⟩
  intro params error setting points first second hopposite
  rw [setting.placedDefect_symm]
  have hbound := combined_line_restored_defect_le_explicit params error (deltaQ error)
    setting points second first hopposite.symm
  have hcard :=
    @FieldModel.card params.q params.model.toFieldModel
  rw [hcard] at hbound
  have hq : (0 : ℝ) < params.q := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos (α := ScalarQ params.toLdParams)
  have hmd : (1 : ℝ) ≤ (params.m * params.d : ℕ) := by
    exact_mod_cast (show 1 ≤ params.m * params.d by
      simpa using Nat.mul_le_mul params.one_le_m params.hd)
  have hdiscard : 1 / (2 * (params.q : ℝ)) ≤
      (params.m * params.d : ℕ) / (params.q : ℝ) := by
    calc
      _ ≤ 1 / (params.q : ℝ) := one_div_le_one_div_of_le hq (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hmd hq.le
  have hμ : (sourceLinePointPairDist params).IsProbability :=
    Distribution.prod_isProbability _ _ (linePointDist_isProbability _) (linePointDist_isProbability _)
  exact (le_min (setting.placedDefect_le_one _ _ _ _ _ hopposite.symm hμ)
    (hbound.trans (add_le_add le_rfl hdiscard))).trans
    (hscalar error _ _ setting.eps_nonneg (by positivity)
      (nondegenerateLinePastingMass_bounds params.toLdParams).1
      (nondegenerateLinePastingMass_bounds params.toLdParams).2)

end

end MIPStarRE.QPBT
