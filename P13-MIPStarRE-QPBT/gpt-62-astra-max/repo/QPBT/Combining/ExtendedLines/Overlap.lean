module

public import QPBT.Combining.ExtendedLines.Measurement
public import QPBT.Combining.SubLineOverlap

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
      (evalOpt sample.2.1 (projX (directPointToPauli point)) polynomials.1,
        evalOpt sample.2.2 (projZ (directPointToPauli point)) polynomials.2) ≤
      (measurement.postprocess (fun pair => some
        ((directPointToPauli point) (alphaVar params.m) * pair.1 +
          (directPointToPauli point) (betaVar params.m) * pair.2))).effect
        ((directEvalOpt sample.1 point
          (sublines.combinedPolynomial sample hsample polynomials)).map
            (extendedDirectScalarEquiv params)) := by
  classical
  have hnoneX (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (none, value) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    simp
  have hnoneZ (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (value, none) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    simp
  cases hevalX : evalOpt sample.2.1 (projX (directPointToPauli point)) polynomials.1 with
  | none =>
    erw [hnoneX]
    apply Quantum.Submeasurement.pos
  | some valueX =>
    cases hevalZ : evalOpt sample.2.2 (projZ (directPointToPauli point)) polynomials.2 with
    | none =>
      erw [hnoneZ]
      apply Quantum.Submeasurement.pos
    | some valueZ =>
      rw [sublines.combinedPolynomial_evalOpt sample hsample polynomials point hpoint
        valueX valueZ hevalX hevalZ]
      have hinjective : Function.Injective
          (fun pair : PauliScalar params × PauliScalar params => (some pair.1, some pair.2)) := by
        intro left right hequal
        grind
      erw [SandwichProduct.postprocess_effect_of_injective measurement _ hinjective
        (valueX, valueZ)]
      exact Finset.single_le_sum (fun pair _ => measurement.pos pair)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- Uniform parameter resampling preserves the full direct line-point law,
including its canonical line, rather than merely its point marginal. -/
theorem avgOver_directLinePointDist_resample_parameter (params : DirectLdParams)
    (quantity : DirectLineDesc params × (DirectPoint params) → ℝ) :
    avgOver (directLinePointDist params) quantity =
      avgOver ((directLinePointDist params).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ params)) (fun parameter =>
          quantity (line, line.base + parameter • line.direction))) := by
  classical
  simp [Distribution.avgOver_map, directLinePointDist, avgOver_mix]
  congr 1
  · congr 1
    unfold directALinePointDist
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (coordinateDirection index)
        (fun base point => quantity
          (.axis (lineRepMap (coordinateDirection index) base) index
            (lineRepMap_apply_self _ _), point))
  · congr 1
    unfold directDLinePointDist
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_uniform_lineRepMap_resample_parameter (directPrefixProjection index direction)
        (fun base point => quantity
          (.diagonal (lineRepMap (directPrefixProjection index direction) base) index
            (directPrefixProjection index direction) (lineRepMap_apply_self _ _)
            (by intro coordinate hbefore; simp [directPrefixProjection, hbefore]), point))

section

variable {params : AdmissibleParams} {error : ℝ}

/-- Real scalar multiplication commutes with placement. -/
private theorem place_real_smul
    (setting : ProjectiveSetting params error) (placement : Placement) (scalar : ℝ)
    (operator : Op (setting.ExpandedLocalSpace placement.side)) :
    setting.place placement (scalar • operator) = scalar • setting.place placement operator := by
  ext row column
  cases placement <;> simp only [ProjectiveSetting.place, Matrix.smul_apply, Complex.real_smul] <;>
    ring

/-- A placed overlap is linear in an averaged left operator. -/
private theorem placed_overlap_average
    {Sample : Type*} (setting : ProjectiveSetting params error) (first second : Placement)
    (law : Distribution Sample) (family : Sample → Op (setting.ExpandedLocalSpace first.side))
    (right : Op (setting.ExpandedLocalSpace second.side)) :
    stateQForm setting.psiHat
      (setting.place first (averageOperatorOverDistribution law family) *
        setting.place second right) =
      avgOver law (fun sample => stateQForm setting.psiHat
        (setting.place first (family sample) * setting.place second right)) := by
  unfold averageOperatorOverDistribution avgOver
  rw [setting.place_finset_sum, Finset.sum_mul, stateQForm_finset_sum]
  congr 1 with sample
  simp [place_real_smul]
  have hscalar (operator : Op (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
      law.weight sample • operator = (law.weight sample : ℂ) • operator := by
    rfl
  rw [hscalar]
  simp only [stateQForm, WinImplications.applyOperatorToState_smul_op, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- On opposite registers a positive left effect preserves order in the right
effect. This applies to both directed player placements without exchanging spaces. -/
private theorem placed_overlap_mono
    (setting : ProjectiveSetting params error) (first second : Placement)
    (hopposite : first.IsOpposite second)
    (left : Op (setting.ExpandedLocalSpace first.side))
    (lower upper : Op (setting.ExpandedLocalSpace second.side))
    (hleft : 0 ≤ left) (hright : lower ≤ upper) :
    stateQForm setting.psiHat (setting.place first left * setting.place second lower) ≤
      stateQForm setting.psiHat (setting.place first left * setting.place second upper) := by
  have hpositive := setting.place_mul_place_nonneg first second hopposite hleft
    (sub_nonneg.mpr hright)
  rw [setting.place_sub, mul_sub] at hpositive
  exact quadratic_form_mono (sub_nonneg.mp hpositive) setting.psiHat

end

/-- Expand the actual conditional extended-line POVM in a placed overlap.
This is exactly the averaging step at paper lines 1118--1134. -/
theorem SubLineWitness.extendedMeasurement_overlap {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (line : DirectLineDesc params.extendedDirectLd)
    (point : DirectPoint params.extendedDirectLd)
    (right : Option (PauliScalar params) → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ answer, stateQForm setting.psiHat
      (setting.place first (((sublines.extendedMeasurement lines first.side line).postprocess
        (fun polynomial => (directEvalOpt line point polynomial).map
          (extendedDirectScalarEquiv params))).effect answer) *
            setting.place second (right answer))) =
      avgOver (sublines.conditionalLaw line) (fun sample =>
        ∑ pair, stateQForm setting.psiHat
          (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
            setting.place second (right ((directEvalOpt line point
              (sublines.combinedPolynomial sample.val
                (Finset.mem_filter.mp sample.property).1 pair)).map
                  (extendedDirectScalarEquiv params))))) := by
  rw [placed_overlap_postprocess]
  change (∑ polynomial, stateQForm setting.psiHat
    (setting.place first (averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => ((lines.T first.side sample.val.2.1 sample.val.2.2).postprocess
        (sublines.combinedPolynomial sample.val
          (Finset.mem_filter.mp sample.property).1)).effect polynomial)) *
      _)) = _
  simp_rw [placed_overlap_average]
  rw [← avgOver_sum]
  apply avgOver_congr
  intro sample
  apply placed_overlap_postprocess

section

variable {params : AdmissibleParams} {error pointError lineError : ℝ}
  (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
  (lines : CombinedLinesWitness setting points lineError)

/-- The actual paired-line versus point-pair overlap on one subline triple,
with its uniform affine parameter. This is the integrand of the first route. -/
def pairedSublineOverlap (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
    let point := directPointToPauli (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second (((points.Q second.side (projX point) (projZ point)).postprocess
          (fun values => (some values.1, some values.2))).effect
            (evalOpt sample.2.1 (projX point) pair.1,
              evalOpt sample.2.2 (projZ point) pair.2))))

/-- The actual extended-line versus extended-point overlap. Both families use
the supplied witnesses and the source polynomial combination. -/
def extendedPointOverlap (sublines : SubLineWitness params)
    (first second : Placement)
    (sample : DirectLineDesc params.extendedDirectLd ×
      (DirectPoint params.extendedDirectLd)) : ℝ :=
  ∑ answer, stateQForm setting.psiHat
    (setting.place first (((sublines.extendedMeasurement lines first.side sample.1).postprocess
      (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
        (extendedDirectScalarEquiv params))).effect answer) *
      setting.place second (((points.Q second.side
        (projX (directPointToPauli sample.2))
        (projZ (directPointToPauli sample.2))).postprocess (fun values => some
          ((directPointToPauli sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli sample.2) (betaVar params.m) * values.2))).effect answer))

end

/-- The completed point-effect comparison survives conditional averaging and
placement on either directed opposite register pair. -/
theorem SubLineWitness.extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (line : DirectLineDesc params.extendedDirectLd)
    (point : DirectPoint params.extendedDirectLd)
    (hpoint : point ∈ line.pointSet) :
    avgOver (sublines.conditionalLaw line) (fun sample =>
      ∑ pair, stateQForm setting.psiHat
        (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
          setting.place second (((points.Q second.side
            (projX (directPointToPauli point))
            (projZ (directPointToPauli point))).postprocess
              (fun values => (some values.1, some values.2))).effect
                (evalOpt sample.val.2.1 (projX (directPointToPauli point)) pair.1,
                  evalOpt sample.val.2.2 (projZ (directPointToPauli point)) pair.2)))) ≤
      extendedPointOverlap setting points lines sublines first second (line, point) := by
  rw [extendedPointOverlap, sublines.extendedMeasurement_overlap]
  apply avgOver_mono
  intro sample
  apply Finset.sum_le_sum
  intro pair _
  apply placed_overlap_mono setting first second hopposite _ _ _
    ((lines.T first.side sample.val.2.1 sample.val.2.2).pos pair)
  have hline := (Finset.mem_filter.mp sample.property).2
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hcomparison := sublines.completedPoint_effect_le sample.val hsample pair point (by simp_all)
    (points.Q second.side (projX (directPointToPauli point))
      (projZ (directPointToPauli point)))
  rw [hline] at hcomparison
  exact hcomparison

/-- The actual extended-line average dominates the first-route paired overlap.
This integrates the source conditional POVM without assuming any joint product
law for projected points. It holds for all directed opposite placements. -/
theorem SubLineWitness.avgOver_extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (pairedSublineOverlap setting points lines first second) ≤
      avgOver (directLinePointDist params.extendedDirectLd)
        (extendedPointOverlap setting points lines sublines first second) := by
  rw [avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal,
    ← sublines.avgOver_conditionalLaw]
  apply avgOver_mono
  intro line
  unfold pairedSublineOverlap
  rw [avgOver_comm]
  apply avgOver_mono
  intro parameter
  refine le_trans ?_ (sublines.extendedPointOverlap_ge lines first second hopposite line _ ⟨parameter, rfl⟩)
  apply le_of_eq
  apply avgOver_congr
  intro sample
  rw [(Finset.mem_filter.mp sample.property).2]

/-- The completed consistency defect of the actual extended-line POVM is
bounded by the first-route deficit, for both player placements. -/
theorem SubLineWitness.extended_consistencyDefect_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    consistencyDefect (directLinePointDist params.extendedDirectLd)
      (fun sample answer => setting.place first
        (((sublines.extendedMeasurement lines first.side sample.1).postprocess
          (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
            (extendedDirectScalarEquiv params))).effect answer))
      (fun sample answer => setting.place second
        (((points.Q second.side (projX (directPointToPauli sample.2))
          (projZ (directPointToPauli sample.2))).postprocess (fun values => some
            ((directPointToPauli sample.2) (alphaVar params.m) * values.1 +
              (directPointToPauli sample.2) (betaVar params.m) * values.2))).effect answer))
      setting.psiHat ≤ 1 - avgOver sublines.D
        (pairedSublineOverlap setting points lines first second) := by
  erw [consistencyDefect_eq_one_sub_overlap (μ := _)
    (fun sample => setting.placedMeasurement first
      ((sublines.extendedMeasurement lines first.side sample.1).postprocess
        (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
          (extendedDirectScalarEquiv params))))
    (fun sample => setting.placedMeasurement second
      ((points.Q second.side (projX (directPointToPauli (P := params) sample.2))
        (projZ (directPointToPauli (P := params) sample.2))).postprocess (fun values => some
          ((directPointToPauli (P := params) sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli (P := params) sample.2) (betaVar params.m) * values.2))))
    (ψ := setting.psiHat) (directLinePointDist_isProbability _) setting.psiHat_norm]
  solve_by_elim [sub_le_sub_left, sublines.avgOver_extendedPointOverlap_ge]

/-- Regroup the subline answers by their two evaluations. -/
theorem SubLineWitness.mean_completed {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP) (first second : Placement) :
    sublines.meanOverlap lines first second (fun v => (points.completed second.side v).effect) =
      avgOver sublines.D (pairedSublineOverlap S points lines first second) := by
  simp only [meanOverlap, evalLaw, subLinePointDist, Distribution.avgOver_map, avgOver_prod,
    lineOverlap, CombinedLinesWitness.evaluated, placed_overlap_postprocess]
  rfl

end
end MIPStarRE.QPBT
