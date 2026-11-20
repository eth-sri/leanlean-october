module

public import QPBT.Combining.Lines

/-!
# Conditional extended-line measurements

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

/-- A positive atom gives a positive atom of every push-forward. -/
private theorem map_weight_pos_of_weight_pos {Source Target : Type*}
    [DecidableEq Target] (law : Distribution Source) (mapping : Source → Target)
    (sample : Source) (hpositive : 0 < law.weight sample) :
    0 < (law.map mapping).weight (mapping sample) := by
  classical
  refine hpositive.trans_le (Finset.single_le_sum
    (fun other _ => law.nonnegative other) (Finset.mem_filter.mpr ⟨?_, rfl⟩))
  by_contra hnot
  simp_all [law.outsideSupport]

/-- Every canonical direct line has positive marginal mass. In particular, the
conditional distribution in the construction at paper lines 1118--1132 is defined
on every direct line, including zero-direction diagonal lines. -/
theorem directLinePointDist_line_weight_pos (params : DirectLdParams)
    (line : DirectLineDesc params) :
    0 < ((directLinePointDist params).map Prod.fst).weight line := by
  have huniform (sample : DirectLdSpace params) :
      0 < (uniformDistribution (DirectLdSpace params)).weight sample := by
    rw [uniformDistribution_weight_apply]
    positivity
  suffices hpoint : 0 < (directLinePointDist params).weight (line, line.base) by
    exact map_weight_pos_of_weight_pos _ Prod.fst _ hpoint
  cases line with
  | axis base index baseFixed =>
    let sample : DirectLdSpace params := ⟨base, index, 0⟩
    have haxis := map_weight_pos_of_weight_pos
      _
      (fun source => (directALineDescOf params source, source.point)) sample (huniform sample)
    have hdecode : directALineDescOf params sample = .axis base index baseFixed := by
      simp [directALineDescOf, sample, baseFixed]
    change 0 < (directALinePointDist params).weight _ at haxis
    rw [hdecode] at haxis
    have hother := (directDLinePointDist params).nonnegative
      (DirectLineDesc.axis base index baseFixed, base)
    change 0 < (1 / 2) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    dsimp only [DirectLineDesc.base]
    linarith
  | diagonal base index direction baseFixed prefixZero =>
    let sample : DirectLdSpace params := ⟨base, index, direction⟩
    have hprefix : directPrefixProjection index direction = direction := by
      funext coordinate
      simp_all [directPrefixProjection]
    have hdiagonal := map_weight_pos_of_weight_pos
      _
      (fun source => (directDLineDescOf params source, source.point)) sample (huniform sample)
    have hdecode : directDLineDescOf params sample =
        .diagonal base index direction baseFixed prefixZero := by
      simp [directDLineDescOf, sample, hprefix, baseFixed]
    change 0 < (directDLinePointDist params).weight _ at hdiagonal
    rw [hdecode] at hdiagonal
    have hother := (directALinePointDist params).nonnegative
      (DirectLineDesc.diagonal base index direction baseFixed prefixZero, base)
    change 0 < (1 / 2) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    dsimp only [DirectLineDesc.base]
    linarith

section

variable {params : AdmissibleParams} (sublines : SubLineWitness params)
  (line : DirectLineDesc params.extendedDirectLd) (sample : SubLineTriple params)
  (hsample : sample ∈ sublines.D.support)

/-- The supported triples over a fixed extended line. Restricting the carrier
retains the affine compatibility proof without choosing any substitute lines. -/
abbrev SubLineWitness.Fiber :=
  ↥(sublines.D.support.filter (fun sample => sample.1 = line))

/-- The mass of a subline fiber is positive by the prescribed extended marginal. -/
theorem SubLineWitness.fiber_mass_pos :
    0 < (sublines.D.map Prod.fst).weight line := by
  rw [sublines.extended_marginal]
  apply directLinePointDist_line_weight_pos

/-- The genuine conditional law of the supported subline triples given their
extended line, as in paper lines 1118--1132. There is no zero-mass branch. -/
def SubLineWitness.conditionalLaw :
    Distribution (sublines.Fiber line) where
  support := Finset.univ
  weight sample := sublines.D.weight sample.val / (sublines.D.map Prod.fst).weight line
  nonnegative sample := div_nonneg (sublines.D.nonnegative sample.val)
    (sublines.fiber_mass_pos line).le
  outsideSupport sample hnot := (hnot (Finset.mem_univ sample)).elim

/-- Conditioning on an extended line preserves total mass one. -/
theorem SubLineWitness.conditionalLaw_isProbability :
    (sublines.conditionalLaw line).IsProbability := by
  change (∑ sample : sublines.Fiber line,
    sublines.D.weight sample.val / _) = 1
  rw [← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (sublines.fiber_mass_pos line).ne'

include hsample in
/-- Supported subline triples supply all eight affine coordinates in the
polynomial combination formula; the choice is only of proved compatible data. -/
private theorem SubLineWitness.exists_affineData :
    ∃ data : Fin 8 → PauliScalar params,
      IsCombineLineCompatible (directPointToPauli sample.1.base)
        (directPointToPauli sample.1.direction)
        sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
        (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) := by
  obtain ⟨offsetX, slopeX, offsetZ, slopeZ, alpha, alphaSlope, beta, betaSlope, hcompat⟩ :=
    sublines.compatibility sample hsample
  exact ⟨![offsetX, slopeX, offsetZ, slopeZ, alpha, alphaSlope, beta, betaSlope], hcompat⟩

include hsample in
/-- Affine coordinates for the actual subline triple, not a replacement POVM. -/
def SubLineWitness.affineData : Fin 8 → PauliScalar params :=
  Classical.choose (show
    ∃ data : Fin 8 → PauliScalar params,
      IsCombineLineCompatible (directPointToPauli sample.1.base)
        (directPointToPauli sample.1.direction)
        sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
        (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) from by
    exact sublines.exists_affineData sample hsample)

end

variable {Scalar : Type*} {params : AdmissibleParams} [Field Scalar] {bound : ℕ}
  {error pointError lineError : ℝ} {setting : ProjectiveSetting params error} {degree : ℕ}
  {points : CombinedPointsWitness setting pointError} (sublines : SubLineWitness params)
  (sample : SubLineTriple params) (hsample : sample ∈ sublines.D.support)
  (lines : CombinedLinesWitness setting points lineError) (side : PlayerSide)
  (line : DirectLineDesc params.extendedDirectLd)

/-- The selected coordinates satisfy the source's affine line identities. -/
theorem SubLineWitness.affineData_compatible :
    let data := sublines.affineData sample hsample
    IsCombineLineCompatible (directPointToPauli sample.1.base)
      (directPointToPauli sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) :=
  Classical.choose_spec (sublines.exists_affineData sample hsample)

include hsample in
/-- The source polynomial combination on a supported triple, transported only
along the canonical identification of the two scalar models. -/
def SubLineWitness.combinedPolynomial
    (polynomials : PauliLinePoly params ×
      PauliLinePoly params) :
    DirectDegPoly params.extendedDirectLd (params.m * params.d + 1) :=
  let data := sublines.affineData sample hsample
  fun index => (extendedDirectScalarEquiv params).symm
    (combineLinePoly (data 0) (data 1) (data 2) (data 3)
      (data 4) (data 5) (data 6) (data 7) polynomials.1 polynomials.2 index)

/-- The directly indexed form of the extended-line POVM at paper lines
1118--1132: condition the subline law and average the postprocessed paired-line POVMs. -/
def SubLineWitness.extendedMeasurement :
    Quantum.Measurement (DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
      (setting.ExpandedLocalSpace side) := by
  let family (sample : sublines.Fiber line) :=
    (lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val (Finset.mem_filter.mp sample.property).1)
  have hsum : (∑ polynomial, averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => (family sample).effect polynomial)) = 1 := by
    rw [← averageOperatorOverDistribution_sum]
    simp only [Quantum.Measurement.sum_eq_one]
    exact averageOperatorOverDistribution_const_of_isProbability _
      (sublines.conditionalLaw_isProbability line) 1
  exact { effect := fun polynomial => averageOperatorOverDistribution
            (sublines.conditionalLaw line) (fun sample => (family sample).effect polynomial)
          pos := fun polynomial => averageOperatorOverDistribution_nonneg _ _
            (fun sample => (family sample).pos polynomial)
          sum_le_one := le_of_eq hsum
          sum_eq_one := hsum }

/-- Integrating the conditional law recovers the original subline law.
This is finite disintegration, not an independence assertion about projections. -/
theorem SubLineWitness.avgOver_conditionalLaw (quantity : SubLineTriple params → ℝ) :
    avgOver (sublines.D.map Prod.fst) (fun line =>
      avgOver (sublines.conditionalLaw line) (fun sample => quantity sample.val)) =
        avgOver sublines.D quantity := by
  classical
  simp only [avgOver, SubLineWitness.conditionalLaw]
  calc
    _ =
        _ := by
      congr 1 with line
      rw [Finset.mul_sum]
      trans ∑ sample : sublines.Fiber line, sublines.D.weight sample.val * quantity sample.val
      · grind [(sublines.fiber_mass_pos line).ne']
      · exact Finset.sum_coe_sort
          (sublines.D.support.filter (fun sample => sample.1 = line))
          (fun sample => sublines.D.weight sample * quantity sample)
    _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun sample hsample => Finset.mem_image.mpr ⟨sample, hsample, rfl⟩) _

/-- A determined direct evaluation gives precisely its completed answer. -/
private theorem directEvalOpt_eq_some_of_evaluatesTo {params : DirectLdParams} {bound : ℕ}
    (line : DirectLineDesc params) (polynomial : DirectDegPoly params bound)
    (point : DirectPoint params) (value : DirectScalarQ params)
    (heval : DirectEvaluatesTo line polynomial point value) :
    directEvalOpt line point polynomial = some value := by
  classical
  have hexists : ∃ answer, _ := ⟨value, heval⟩
  rw [directEvalOpt, dif_pos hexists]
  obtain ⟨parameter, hparameter⟩ := heval.1
  exact congrArg some (((Classical.choose_spec hexists).2 parameter hparameter).symm.trans
    (heval.2 parameter hparameter))

/-- Evaluation commutes with the canonical scalar identification. -/
private theorem evalCoefficient_extendedScalar
    (polynomial : DirectDegPoly params.extendedDirectLd bound)
    (parameter : DirectScalarQ params.extendedDirectLd) :
    extendedDirectScalarEquiv params (evalCoefficient polynomial parameter) =
      evalCoefficient (fun index => extendedDirectScalarEquiv params (polynomial index))
        (extendedDirectScalarEquiv params parameter) := by
  rfl

/-- If both projected polynomials have determined values, their actual combined
polynomial has the required determined value at the extended point. This also
covers zero-direction lines: every parameter is checked, rather than selecting
one parameter or assigning a field-valued fallback. -/
theorem SubLineWitness.combinedPolynomial_evaluatesTo
    (polynomials : PauliLinePoly params ×
      PauliLinePoly params)
    (point : DirectPoint params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : PauliScalar params)
    (hevalX : EvaluatesTo sample.2.1 polynomials.1
      (projX (directPointToPauli point)) valueX)
    (hevalZ : EvaluatesTo sample.2.2 polynomials.2
      (projZ (directPointToPauli point)) valueZ) :
    DirectEvaluatesTo sample.1 (sublines.combinedPolynomial sample hsample polynomials) point
      ((extendedDirectScalarEquiv params).symm
        ((directPointToPauli point) (alphaVar params.m) * valueX +
          (directPointToPauli point) (betaVar params.m) * valueZ)) := by
  obtain ⟨initialParameter, hinitial⟩ := hpoint
  refine ⟨⟨initialParameter, hinitial⟩, ?_⟩
  intro parameter hparameter
  let data := sublines.affineData sample hsample
  have hcompat := sublines.affineData_compatible sample hsample
  have hformula := combineLinePoly_spec
    _ _
    sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
    _ _ _ _ _ _ _ _
    polynomials.1 polynomials.2 hcompat (extendedDirectScalarEquiv params parameter)
  have hpointTransport : directPointToPauli point =
      directPointToPauli sample.1.base +
        extendedDirectScalarEquiv params parameter •
          directPointToPauli sample.1.direction := by
    assumption
  apply (extendedDirectScalarEquiv params).injective
  rw [evalCoefficient_extendedScalar, RingEquiv.apply_symm_apply]
  simp [SubLineWitness.combinedPolynomial]
  rw [hformula.2.2]
  erw [(hevalX.2 _ (hpointTransport ▸ hformula.1)), (hevalZ.2 _ (hpointTransport ▸ hformula.2.1))]
  simp [hpointTransport, hcompat.1, hcompat.2.1, hcompat.2.2.1, hcompat.2.2.2.1]

/-- Completed evaluation of the actual combination agrees with the source
linear combination whenever both source evaluations are defined. -/
theorem SubLineWitness.combinedPolynomial_evalOpt
    (polynomials : PauliLinePoly params ×
      PauliLinePoly params)
    (point : DirectPoint params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : PauliScalar params)
    (hevalX : evalOpt sample.2.1 (projX (directPointToPauli point)) polynomials.1 =
      some valueX)
    (hevalZ : evalOpt sample.2.2 (projZ (directPointToPauli point)) polynomials.2 =
      some valueZ) :
    (directEvalOpt sample.1 point (sublines.combinedPolynomial sample hsample polynomials)).map
      (extendedDirectScalarEquiv params) =
        some ((directPointToPauli point) (alphaVar params.m) * valueX +
          (directPointToPauli point) (betaVar params.m) * valueZ) := by
  rw [directEvalOpt_eq_some_of_evaluatesTo _ _ _ _
    (sublines.combinedPolynomial_evaluatesTo sample hsample polynomials point hpoint valueX valueZ
      ((evalOpt_eq_some_iff _ _ _ _).mp hevalX) ((evalOpt_eq_some_iff _ _ _ _).mp hevalZ))]
  simp

/-- Coefficient support bounds the degree of the represented polynomial. -/
private theorem linePolynomial_natDegree_le_of_coefficients {polynomial : Fin (bound + 1) → Scalar}
    (hdegree : ∀ index, degree < index.val → polynomial index = 0) :
    (linePolynomialOfCoefficients polynomial).natDegree ≤ degree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  by_cases hindex : index.val ≤ degree
  · apply Polynomial.natDegree_mul_le.trans
    simp_all
  · simp_all

/-- Affine substitution preserves a degree bound. -/
private theorem affine_comp_natDegree_le
    {polynomial : Polynomial Scalar} (offset slope : Scalar) {degree : ℕ}
    (hdegree : polynomial.natDegree ≤ degree) :
    (polynomial.comp (Polynomial.C offset + Polynomial.C slope * Polynomial.X)).natDegree ≤
      degree := by
  have haffine : (Polynomial.C offset + Polynomial.C slope * Polynomial.X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  exact Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hdegree haffine)

/-- The source combination has degree at most `degree` on an axis line:
either the two scalar coordinates are constant, or both projected parameters
are constant. This is the algebraic assertion at paper lines 1127--1132. -/
theorem combineLinePoly_axis_degree
    (hdegree : 1 ≤ degree) (data : Fin 8 → Scalar)
    (polynomialX polynomialZ : Fin (bound + 1) → Scalar)
    (hdegreeX : ∀ index, degree < index.val → polynomialX index = 0)
    (hdegreeZ : ∀ index, degree < index.val → polynomialZ index = 0)
    (haxis : (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0)) :
    ∀ index : Fin (bound + 1 + 1), degree < index.val →
      combineLinePoly (data 0) (data 1) (data 2) (data 3)
        (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ index = 0 := by
  have htotal : (combineLinePolynomial (data 0) (data 1) (data 2) (data 3)
      (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ).natDegree ≤ degree := by
    unfold combineLinePolynomial
    rcases haxis with ⟨halpha, hbeta⟩ | ⟨hparamX, hparamZ⟩
    · simp_all
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · apply Polynomial.natDegree_mul_le.trans
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le (data 0) (data 1) (linePolynomial_natDegree_le_of_coefficients hdegreeX))
      · apply Polynomial.natDegree_mul_le.trans
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le (data 2) (data 3) (linePolynomial_natDegree_le_of_coefficients hdegreeZ))
    · simp_all
      have hterm (constant slope value : Scalar) :
          ((Polynomial.C constant + Polynomial.C slope * Polynomial.X) *
            Polynomial.C value).natDegree ≤ degree := by
        apply Polynomial.natDegree_mul_le.trans
        simp only [Polynomial.natDegree_C, Nat.add_zero]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
          (Polynomial.natDegree_mul_le.trans (by simpa using hdegree)))
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (hterm _ _ _) (hterm _ _ _))
  intro index hindex
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (htotal.trans_lt hindex)

/-- Axis directions in the source line carrier are nonzero. -/
private theorem source_axis_direction_ne_zero {params : LdParams}
    {line : LineDesc params} (haxis : line.kind = .axis) : line.direction ≠ 0 := by
  cases line with
  | axis base seed baseFixed =>
    simp [LineDesc.direction, coordinateDirection]
  | diagonal => cases haxis

/-- Two equal points on a nonzero affine direction force the parameter slope to vanish. -/
private theorem affine_slope_eq_zero {dimension : ℕ}
    {point base direction : Fin dimension → Scalar} {offset slope : Scalar}
    (hdirection : direction ≠ 0) (hzero : point = base + offset • direction)
    (hone : point = base + (offset + slope) • direction) : slope = 0 := by
  simp_all [add_smul]

/-- Axis subline coordinates satisfy the source's constant-coordinate alternative. -/
theorem SubLineWitness.affineData_axis (haxis : sample.1.kind = .axis) :
    let data := sublines.affineData sample hsample
    (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0) := by
  have hcompat := sublines.affineData_compatible sample hsample
  have hsource := sublines.axis_closure sample hsample haxis
  have hcoordinate : directPointToPauli sample.1.direction =
      coordinateDirection sample.1.index := by
    rcases sample with ⟨line, pair⟩
    cases line with
    | axis => apply directPointToPauli_coordinateDirection
    | diagonal => cases haxis
  by_cases hspecial : sample.1.index = alphaVar params.m ∨ sample.1.index = betaVar params.m
  · right
    have hprojection : projX (directPointToPauli sample.1.direction) = 0 ∧
        projZ (directPointToPauli sample.1.direction) = 0 := by
      rw [hcoordinate]
      rcases hspecial with halpha | hbeta
      · rw [halpha]
        exact ⟨projX_coordinateDirection_alphaVar, projZ_coordinateDirection_alphaVar⟩
      · rw [hbeta]
        exact ⟨projX_coordinateDirection_betaVar, projZ_coordinateDirection_betaVar⟩
    have hzero := hcompat.2.2.2.2 0
    have hone := hcompat.2.2.2.2 1
    simp at hzero
    simp [one_smul, projX_add, projZ_add, hprojection.1, hprojection.2] at hone
    exact ⟨affine_slope_eq_zero
      (source_axis_direction_ne_zero hsource.1) hzero.1 hone.1,
      affine_slope_eq_zero
        (source_axis_direction_ne_zero hsource.2) hzero.2 hone.2⟩
  · left
    rw [← hcompat.2.1, ← hcompat.2.2.2.1, hcoordinate]
    simp [coordinateDirection, (Ne.symm (not_or.mp hspecial).1), (Ne.symm (not_or.mp hspecial).2)]

/-- The actual polynomial combination preserves the source axis-degree support. -/
theorem SubLineWitness.combinedPolynomial_axis_degree (haxis : sample.1.kind = .axis)
    (polynomials : PauliLinePoly params ×
      PauliLinePoly params)
    (hdegreeX : polynomials.1.FitsDegree params.d)
    (hdegreeZ : polynomials.2.FitsDegree params.d) :
    ∀ index, params.d < index.val →
      sublines.combinedPolynomial sample hsample polynomials index = 0 := by
  intro index hindex
  change (extendedDirectScalarEquiv params).symm _ = 0
  erw [(combineLinePoly_axis_degree params.hd _
    polynomials.1 polynomials.2 hdegreeX hdegreeZ
    (sublines.affineData_axis sample hsample haxis) index hindex)]
  exact map_zero _

/-- The conditional average of the actual paired-line POVMs has no outcomes
above degree `d` on an extended axis line, as asserted at paper lines 1127--1132. -/
theorem SubLineWitness.extendedMeasurement_axis_degree
    (polynomial : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (haxis : line.kind = .axis) (hdegree : ¬ ∀ index, params.d < index.val → polynomial index = 0) :
    (sublines.extendedMeasurement lines side line).effect polynomial = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro sample _
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hsampleAxis : sample.val.1.kind = .axis := by
    rw [(Finset.mem_filter.mp sample.property).2]
    exact haxis
  have hsource := sublines.axis_closure sample.val hsample hsampleAxis
  suffices hzero : ((lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val hsample)).effect polynomial = 0 by
    exact (congrArg (fun operator => (sublines.conditionalLaw line).weight sample • operator)
      hzero).trans (smul_zero _)
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hdegreeX : pair.1.FitsDegree params.d
  · by_cases hdegreeZ : pair.2.FitsDegree params.d
    · have hfit := sublines.combinedPolynomial_axis_degree sample.val hsample hsampleAxis
        pair hdegreeX hdegreeZ
      rw [(Finset.mem_filter.mp hpair).2] at hfit
      simp_all
    · exact lines.axis_degree_Z side _ _ _ _ hsource.2 hdegreeZ
  · exact lines.axis_degree_X side _ _ _ _ hsource.1 hdegreeX


end

end MIPStarRE.QPBT
