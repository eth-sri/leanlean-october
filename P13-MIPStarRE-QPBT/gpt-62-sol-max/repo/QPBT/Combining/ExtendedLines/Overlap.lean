module

public import QPBT.Combining.ExtendedLines.Measurement
public import QPBT.Combining.SubLineZDeficit
public import QPBT.Combining.Lines.SubLineMixture
public import QPBT.Combining.Lines.SubLineUniform

/-!
# Consistency of the extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- The completed point-pair effect is bounded by the effect of its linear
combination at the actual combined evaluation. Undefined source evaluations
contribute zero on the point side. The statement holds for either player's
measurement without any symmetry assumption on the strategy or local spaces. -/
theorem SubLineWitness.completedPoint_effect_le {params : AdmissibleParams}
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : PauliLinePoly params ×
      PauliLinePoly params)
    (point : DirectPoint params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet)
    (measurement : Quantum.Measurement (PauliScalar params × PauliScalar params) Carrier) :
    (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect
      (evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1,
        evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2) ≤
      (measurement.postprocess (fun pair => some
        ((directPointToPauli params point) (alphaVar params.m) * pair.1 +
          (directPointToPauli params point) (betaVar params.m) * pair.2))).effect
        ((directEvalOpt sample.1 point
          (sublines.combinedPolynomial sample hsample polynomials)).map
            (extendedDirectScalarEquiv params)) := by
  classical
  cases hx : evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1 <;>
    cases hz : evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2
  case some.some x z =>
    rw [sublines.combinedPolynomial_evalOpt sample hsample polynomials point hpoint x z hx hz]
    let f := Prod.map (@Option.some (PauliScalar params)) (@Option.some (PauliScalar params))
    change (measurement.postprocess f).effect (f (x, z)) ≤ _
    rw [SandwichProduct.postprocess_effect_of_injective measurement f
      (Prod.map_injective.mpr ⟨Option.some_injective _, Option.some_injective _⟩)]
    exact SandwichProduct.effect_le_postprocess_effect _ _ _
  all_goals
    rw [SandwichProduct.postprocess_effect_eq_zero_of_notMem _ _ (by simp [Prod.ext_iff])]
    exact Quantum.Submeasurement.pos _ _

/-- Uniform parameter resampling preserves the full direct line-point law,
including its canonical line, rather than merely its point marginal. -/
theorem avgOver_directLinePointDist_resample_parameter (params : DirectLdParams)
    (quantity : DirectLinePointSample params → ℝ) :
    avgOver (directLinePointDist params) quantity =
      avgOver ((directLinePointDist params).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ params)) (fun parameter =>
          quantity (line, line.base + parameter • line.direction))) := by
  classical
  rw [Distribution.avgOver_map, directLinePointDist, avgOver_mix, avgOver_mix]
  congr 1 <;> congr 1
  all_goals
    simp only [directALinePointDist, directDLinePointDist, Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod,
      SandwichProduct.avgOver_distribution_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
  · simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (coordinateDirection index)
        (fun base point => quantity
          (.axis (lineRepMap (coordinateDirection index) base) index
            (lineRepMap_apply_self _ _), point))
  · simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (directPrefixProjection index direction)
        (fun base point => quantity
          (.diagonal (lineRepMap (directPrefixProjection index direction) base) index
            (directPrefixProjection index direction) (lineRepMap_apply_self _ _)
            (by intro coordinate hbefore; simp [directPrefixProjection, hbefore]), point))

/-- Real scalar multiplication commutes with placement. -/
private theorem place_real_smul {params : AdmissibleParams} {error : ℝ}
    (setting : ProjectiveSetting params error) (placement : Placement) (scalar : ℝ)
    (operator : Op (setting.ExpandedLocalSpace placement.side)) :
    setting.place placement (scalar • operator) = scalar • setting.place placement operator :=
  (setting.placeLinear placement).map_smul_of_tower scalar operator

/-- A placed overlap is linear in an averaged left operator. -/
private theorem placed_overlap_average {params : AdmissibleParams} {error : ℝ}
    {Sample : Type*} (setting : ProjectiveSetting params error) (first second : Placement)
    (law : Distribution Sample) (family : Sample → Op (setting.ExpandedLocalSpace first.side))
    (right : Op (setting.ExpandedLocalSpace second.side)) :
    setting.placedCorrelation first second (averageOperatorOverDistribution law family) right =
      avgOver law (fun sample => setting.placedCorrelation first second (family sample) right) := by
  unfold ProjectiveSetting.placedCorrelation averageOperatorOverDistribution avgOver
  rw [setting.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
  simp only [place_real_smul, smul_mul_assoc, stateQForm_real_smul]

/-- Expand the actual conditional extended-line POVM in a placed overlap.
This is exactly the averaging step at paper lines 1118--1134. -/
theorem SubLineWitness.extendedMeasurement_overlap {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (line : DirectLineDesc params.extendedDirectLd)
    (point : DirectPoint params.extendedDirectLd)
    (right : Option (PauliScalar params) → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ answer, setting.placedCorrelation first second
      (((sublines.extendedMeasurement lines first.side line).postprocess
        (fun polynomial => (directEvalOpt line point polynomial).map
          (extendedDirectScalarEquiv params))).effect answer) (right answer)) =
      avgOver (sublines.conditionalLaw line) (fun sample =>
        ∑ pair, setting.placedCorrelation first second
          ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) (right ((directEvalOpt line point
              (sublines.combinedPolynomial sample.val
                (Finset.mem_filter.mp sample.property).1 pair)).map
                  (extendedDirectScalarEquiv params)))) := by
  rw [setting.placed_overlap_postprocess]
  change (∑ polynomial, setting.placedCorrelation first second
    (averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => ((lines.T first.side sample.val.2.1 sample.val.2.2).postprocess
        (sublines.combinedPolynomial sample.val
          (Finset.mem_filter.mp sample.property).1)).effect polynomial)) (right ((directEvalOpt line point polynomial).map
        (extendedDirectScalarEquiv params)))) = _
  simp_rw [placed_overlap_average]
  rw [← avgOver_sum]
  apply avgOver_congr
  intro sample
  exact setting.placed_overlap_postprocess first second _ _ _

section

variable {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError)
include params error pointError lineError setting points lines

/-- The actual paired-line versus point-pair overlap on one subline triple,
with its uniform affine parameter. This is the integrand of the first route. -/
def pairedSublineOverlap (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  sublineOverlap lines first second
    (fun xz o => (points.completedPair second.side xz.1 xz.2).effect o) sample

/-- The actual extended-line versus extended-point overlap. Both families use
the supplied witnesses and the source polynomial combination. -/
def extendedPointOverlap (sublines : SubLineWitness params)
    (first second : Placement)
    (sample : DirectLinePointSample params.extendedDirectLd) : ℝ :=
  ∑ answer, setting.placedCorrelation first second ((ExtendedLineGame.readLineAt
      (sublines.extendedMeasurement lines first.side sample.1) sample.1 sample.2).effect answer) ((ExtendedLineGame.completedPointReadout points second.side sample.2).effect answer)

end

section

variable {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second)
include params error pointError lineError setting points sublines lines first second hopposite

/-- The completed point-effect comparison survives conditional averaging and
placement on either directed opposite register pair. -/
theorem SubLineWitness.extendedPointOverlap_ge
    (line : DirectLineDesc params.extendedDirectLd)
    (point : DirectPoint params.extendedDirectLd)
    (hpoint : point ∈ line.pointSet) :
    avgOver (sublines.conditionalLaw line) (fun sample =>
      ∑ pair, setting.placedCorrelation first second
        ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) (((points.Q second.side
            (projX (directPointToPauli params point))
            (projZ (directPointToPauli params point))).postprocess
              (fun values => (some values.1, some values.2))).effect
                (evalOpt sample.val.2.1 (projX (directPointToPauli params point)) pair.1,
                  evalOpt sample.val.2.2 (projZ (directPointToPauli params point)) pair.2))) ≤
      extendedPointOverlap setting points lines sublines first second (line, point) := by
  rw [extendedPointOverlap, sublines.extendedMeasurement_overlap]
  apply avgOver_mono
  intro sample
  apply Finset.sum_le_sum
  intro pair _
  apply setting.placedCorrelation_mono_right first second hopposite
    ((lines.T first.side sample.val.2.1 sample.val.2.2).pos pair)
  have hline := (Finset.mem_filter.mp sample.property).2
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hpointSample : point ∈ sample.val.1.pointSet := by rw [hline]; exact hpoint
  have hcomparison := sublines.completedPoint_effect_le sample.val hsample pair point hpointSample
    (points.Q second.side (projX (directPointToPauli params point))
      (projZ (directPointToPauli params point)))
  rw [hline] at hcomparison
  simpa only [ExtendedLineGame.completedPointReadout, CombinedPointsWitness.extendedQ,
    ExtendedPointQuestion.ofDirect, ExtendedPointQuestion.read, Measurement.postprocess_comp,
    Function.comp_apply] using hcomparison

/-- The actual extended-line average dominates the first-route paired overlap.
This integrates the source conditional POVM without assuming any joint product
law for projected points. It holds for all directed opposite placements. -/
theorem SubLineWitness.avgOver_extendedPointOverlap_ge :
    avgOver sublines.D (pairedSublineOverlap setting points lines first second) ≤
      avgOver (directLinePointDist params.extendedDirectLd)
        (extendedPointOverlap setting points lines sublines first second) := by
  rw [avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal,
    ← sublines.avgOver_conditionalLaw]
  apply avgOver_mono
  intro line
  unfold pairedSublineOverlap sublineOverlap
  rw [avgOver_comm]
  apply avgOver_mono
  intro parameter
  have hpoint : line.base + parameter • line.direction ∈ line.pointSet := ⟨parameter, rfl⟩
  refine le_trans ?_ (sublines.extendedPointOverlap_ge lines first second hopposite line _ hpoint)
  apply le_of_eq
  apply avgOver_congr
  intro sample
  simp only [SubLineDraw.basePoints, SubLineDraw.linePoints]
  rw [(Finset.mem_filter.mp sample.property).2]

/-- The completed consistency defect of the actual extended-line POVM is
bounded by the first-route deficit, for both player placements. -/
theorem SubLineWitness.extended_consistencyDefect_le :
    ExtendedLineGame.completedDefect points first second (directLinePointDist params.extendedDirectLd)
      (sublines.extendedMeasurement lines first.side) ≤ 1 - avgOver sublines.D
        (pairedSublineOverlap setting points lines first second) := by
  refine le_of_eq_of_le (consistencyDefect_eq_one_sub_overlap (directLinePointDist params.extendedDirectLd)
    (fun z => setting.placedMeasurement first (ExtendedLineGame.readLineAt
      (sublines.extendedMeasurement lines first.side z.1) z.1 z.2))
    (fun z => setting.placedMeasurement second (ExtendedLineGame.completedPointReadout points second.side z.2))
    setting.psiHat (directLinePointDist_isProbability _) setting.psiHat_norm) ?_
  exact sub_le_sub_left (sublines.avgOver_extendedPointOverlap_ge lines first second hopposite) 1

end

/-- The ordered Z-then-X point overlap on the actual subline law. -/
def orderedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  sublineOverlap lines first second (fun xz o =>
    setting.completedPointPairEffect second.side .Z xz o *
      setting.completedPointPairEffect second.side .X xz o) sample

/-- The first-route replacement by the ordered point product holds for any
placement, in particular for the missing second-player orientation. Its only
distributional input is the uniform joint point marginal, not a product law
conditional on the projected lines. -/
theorem SubLineWitness.paired_ordered_overlap_gap_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) :
    |avgOver sublines.D (pairedSublineOverlap setting points lines first second) -
      avgOver sublines.D (orderedSublineOverlap setting points lines first second)| ≤
        Real.sqrt (4 * pointError) := by
  unfold pairedSublineOverlap orderedSublineOverlap
  rw [sublines.avgOver_sublineOverlap_eq, sublines.avgOver_sublineOverlap_eq]
  refine abs_overlap_gap_le_sqrt_of_opFamilyDistSq sublines.drawLaw
    (lines.placedSublineEval first) _ _ setting.psiHat sublines.drawLaw_isProbability
    setting.psiHat_norm _ ?_
  exact points.completedProduct_dist_le second .Z sublines.drawLaw SubLineDraw.basePoints (fun f => by
    rw [SubLineWitness.drawLaw, SandwichProduct.avgOver_distribution_prod]
    exact sublines.avgOver_projX_projZ params f)


end

end MIPStarRE.QPBT
