module

public import QPBT.Combining.Lines.SubLineMixture
public import QPBT.Combining.Points
public import QPBT.Combining.Lines.ConsistencyPositivity
public import QPBT.Games.RestrictedAverage
public import QPBT.Combining.Points.MarginalContraction

/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

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

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step in `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, using `lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : LdParams)
    (value : (LdPoint L) → ℝ) :
    avgOver (linePointDist L) (fun sample => value sample.2) =
      avgOver (uniformDistribution (LdPoint L)) value := by
  rw [linePointDist, avgOver_mix]
  rw [← Distribution.avgOver_map (aLinePointDist L) Prod.snd value,
    ← Distribution.avgOver_map (dLinePointDist L) Prod.snd value,
    lineKindPointDist_point_marginal_uniform L .axis,
    lineKindPointDist_point_marginal_uniform L .diagonal]
  ring

/-- Independent line-point samples have independent uniform point marginals.
This formalization-only identity transports the point estimates in
`eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem avgOver_prod_linePointDist_points (L : LdParams)
    (value : (LdPoint L) × (LdPoint L) → ℝ) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun sample => value (sample.1.2, sample.2.2)) =
      avgOver (uniformDistribution
        ((LdPoint L) × (LdPoint L))) value := by
  rw [uniformDistribution_prod, SandwichProduct.avgOver_distribution_prod,
    SandwichProduct.avgOver_distribution_prod]
  conv_lhs =>
    arg 2
    ext sample
    rw [avgOver_linePointDist_point L (fun point => value (sample.2, point))]
  exact avgOver_linePointDist_point L
    (fun point => avgOver (uniformDistribution _) (fun other => value (point, other)))

/-- Completing both answer alphabets with a zero outcome preserves placed
squared distance. This formalization-only identity reconciles `eq:pasting-q1`
with the completed evaluation convention of `lem:qld-comm-line-cons`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p2.side)) :
    opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  simp only [opFamilyDistSq, Fintype.sum_option, SandwichProduct.postprocess_some_effect,
    SandwichProduct.postprocess_some_effect_none, S.place_zero, sub_self]
  simp [applyOperatorToState]

/-- The completed marginal has the same error on pairs of line-point samples. -/
private theorem marginal_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p q : Placement) (hop : p.IsOpposite q) (W : PauliKind) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
      (fun sample a => S.place p
        ((((points.Q p.side sample.1.2 sample.2.2).postprocess W.component).postprocess some).effect a))
      (fun sample a => S.place q ((S.pointMeasExpOption q.side W (W.component (sample.1.2, sample.2.2))).effect a))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact (avgOver_prod_linePointDist_points P.toLdParams _).le.trans
    (points.marginal_distance_le p q hop W)

/-- On either placement the evaluated line is close to the completed point
measurement. This formalization-only version of the intermediate comparison
in `eq:pasting-q1` retains the strategy error. It follows from
`lem:qld-comm-line-cons` item 3 and `lem:qld-comm-cons` item 1, rather than
identifying measurements on different placements. -/
theorem exp_line_point_same_placement_distance_le_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p1 p2 : Placement), p1.IsOpposite p2 → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side W sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side W sample.2).effect answer))
        S.psiHat ≤ 1040 * (ε + deltaLine ε) := by
  intro P ε S p1 p2 hopp W
  classical
  have hreverse := hopp.symm
  have hpoint : opFamilyDistSq (linePointDist P.toLdParams)
      (fun sample answer => S.place p1
        ((S.pointMeasExpOption p1.side W sample.2).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side W sample.2).effect answer)) S.psiHat ≤ 172 * ε := by
    unfold ProjectiveSetting.pointMeasExpOption
    erw [S.opFamilyDistSq_postprocess_some]
    unfold opFamilyDistSq
    rw [avgOver_linePointDist_point P.toLdParams (fun point =>
      ∑ answer, ‖applyOperatorToState
        (S.place p1 ((S.pointMeasExp p1.side W point).effect answer) -
          S.place p2 ((S.pointMeasExp p2.side W point).effect answer)) S.psiHat‖ ^ 2)]
    exact exp_point_self_cons_explicit P ε S p1 p2 hopp W
  have htri := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
    (exp_line_point_cons_explicit' P ε S p2 p1 hreverse W) hpoint
  refine htri.trans ?_
  have hε := S.eps_nonneg
  have hline : 0 ≤ deltaLine ε := Real.sqrt_nonneg ε
  nlinarith

/-- On independent samples, the selected marginal of the completed joint point
measurement is consistent with the evaluated line in that basis (`eq:pasting-q1`). -/
theorem combined_points_line_marginal_defect_le_explicit
    (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ)
    (p q : Placement) (hop : p.IsOpposite q) (W : PauliKind) :
    S.placedDefect p q
      (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams)) (fun sample => (points.Q p.side sample.1.2 sample.2.2).postprocess
        (fun ab => some (W.component ab))) (fun sample => S.lineEvalMeasExp q.side W (W.component sample).1 (W.component sample).2) ≤ 8 * δQ + 2080 * (ε + deltaLine ε) := by
  classical
  have hh := exp_line_point_same_placement_distance_le_explicit P ε S p q hop W
  let μ := linePointDist P.toLdParams
  let Sample := LinePointSample P.toLdParams
  let F (sample : Sample) := S.lineEvalMeasExp q.side W sample.1 sample.2
  let G (sample : Sample) := S.pointMeasExpOption q.side W sample.2
  have h : opFamilyDistSq (Distribution.prod μ μ)
      (fun sample a => S.place q ((G (W.component sample)).effect a))
      (fun sample a => S.place q ((F (W.component sample)).effect a)) S.psiHat ≤
      1040 * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [Distribution.avgOver_prod]
    have hμ := linePointDist_isProbability P.toLdParams
    cases W <;> simpa only [opFamilyDistSq, F, G, PauliKind.component, avgOver_const_of_isProbability μ hμ] using hh
  let Q (sample : Sample × Sample) := (points.Q p.side sample.1.2 sample.2.2).postprocess
    (fun ab => some (W.component ab))
  refine (consistencyDefect_le_opFamilyDistSq_of_projective (Distribution.prod μ μ)
      (fun sample => S.placedMeasurement p (Q sample))
      (fun sample => S.placedMeasurement q (F (W.component sample))) S.psiHat
      (fun sample => S.placedMeasurement_isProjective p _
        (SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _))
      (fun sample => S.placedMeasurement_isProjective q _
        (SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))).trans ?_
  have hpoint := marginal_option_linePoint_distance_le points p q hop W
  simp only [Measurement.postprocess_comp] at hpoint
  have hm : ∀ xz : (LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams),
      W.component (xz.1.2, xz.2.2) = (W.component xz).2 := by
    cases W <;> intro xz <;> rfl
  simp only [hm] at hpoint
  exact (opFamilyDistSq_le_of_le_of_le _ _ _ _ _ _ _ hpoint h).trans (by ring_nf; rfl)

end

end MIPStarRE.QPBT
