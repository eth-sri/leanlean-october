module

public import NearlyMinimax.CardinalSeparatedKernel

@[expose] public section

/-! Genuine positive separated mark measures for interpolation bands. Two
positive copies with opposite symmetric matrix marks suffice; their cost
is bounded by twice the upper-cutoff cost. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev CardinalBandMark (d n : ℕ) := Bool × CardinalSeparatedMark d n

def cardinalBandMeasure (d n : ℕ) (L T : ℝ) : Measure (CardinalBandMark d n) :=
  Measure.map (fun z => (false, z)) (cardinalSeparatedMeasure d n T) +
    Measure.map (fun z => (true, z)) (cardinalSeparatedMeasure d n (max 1 L))

section
variable {d n D : ℕ} (lam L T : ℝ) {f : CardinalBandMark d n → ℝ} (hf : Measurable f)
    (hT : Integrable (fun z => f (false, z)) (cardinalSeparatedMeasure d n T))
    (hL : Integrable (fun z => f (true, z)) (cardinalSeparatedMeasure d n (max 1 L)))

def cardinalBandAmplitude (z : CardinalBandMark d n)
    (β β' : HighFrameIndex d D) : ℝ :=
  if z.1 then -cardinalSeparatedAmplitude lam z.2 β β' else cardinalSeparatedAmplitude lam z.2 β β'

def cardinalBandFactor (z : CardinalBandMark d n)
    (l : Fin n) (x : Covariate d) : ℝ := cardinalSeparatedFactor lam z.2 l x

theorem cardinal_band_mark_standardBorel (d n : ℕ) : StandardBorelSpace (CardinalBandMark d n) := by
  letI := cardinal_separated_mark_standardBorel d n
  infer_instance

theorem cardinal_band_measure_finite (d n : ℕ) (L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalBandMeasure d n L T) := by
  letI := cardinal_separated_measure_finite d n hT
  letI := cardinal_separated_measure_finite d n (le_max_left 1 L)
  unfold cardinalBandMeasure
  infer_instance

theorem cardinal_band_amplitude_measurable (β β' : HighFrameIndex d D) :
    Measurable (fun z : CardinalBandMark d n => cardinalBandAmplitude lam z β β') := by
  apply Measurable.ite
  · exact measurable_fst (measurableSet_singleton true)
  · exact ((cardinal_separated_amplitude_measurable lam β β').comp measurable_snd).neg
  · exact (cardinal_separated_amplitude_measurable lam β β').comp measurable_snd

include hf hT hL in
theorem cardinal_band_integrable_of_copies :
    Integrable f (cardinalBandMeasure d n L T) := by
  apply integrable_add_measure.mpr
  constructor
  · exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_const.prodMk measurable_id).aemeasurable).mpr hT
  · exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_const.prodMk measurable_id).aemeasurable).mpr hL

include hf hT hL in
theorem cardinal_band_integral_eq_copies :
    (∫ z, f z ∂cardinalBandMeasure d n L T) =
      (∫ z, f (false, z) ∂cardinalSeparatedMeasure d n T) +
        (∫ z, f (true, z) ∂cardinalSeparatedMeasure d n (max 1 L)) := by
  have hmF : Measurable (fun z : CardinalSeparatedMark d n => (false, z)) := by fun_prop
  have hmL : Measurable (fun z : CardinalSeparatedMark d n => (true, z)) := by fun_prop
  unfold cardinalBandMeasure
  rw [integral_add_measure ((integrable_map_measure hf.aestronglyMeasurable hmF.aemeasurable).mpr hT) ((integrable_map_measure hf.aestronglyMeasurable hmL.aemeasurable).mpr hL),
    integral_map hmF.aemeasurable hf.aestronglyMeasurable,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable]

theorem cardinal_band_cost_eq (z : CardinalBandMark d n) :
    separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z =
      separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z.2 := by
  unfold separatedMatrixCost cardinalBandAmplitude
  cases z.1 <;> simp

theorem cardinal_band_cost_integrable {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalBandAmplitude (D := D) lam)) (cardinalBandMeasure d n L T) := by
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs))
  apply cardinal_band_integrable_of_copies L T hm
  · exact cardinal_separated_cost_integrable lam hT
  · simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam (le_max_left 1 L)

end

variable {d n D : ℕ} (hn : 2 ≤ n) (i : Fin n) (lam : ℝ) {L : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam)
    (U : DesignSample d n)

include hn in
theorem cardinal_band_cost_integral_le (L : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (hLT : L ≤ T) :
    let scale := (1024 * |lam| * d ^ 2) ^ (n - 1)
    (∫ z, separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z ∂cardinalBandMeasure d n L T) ≤
      2 * n * scale * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  intro scale
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs))
  rw [cardinal_band_integral_eq_copies L T hm
    (cardinal_separated_cost_integrable lam hT)
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam (le_max_left 1 L))]
  simp_rw [cardinal_band_cost_eq]
  have hsmall : n * scale * (max 1 L) ^ 2 *
      (1 + Real.log (max 1 L)) ^ (n - 2) ≤
      n * scale * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
    bound
  have h := add_le_add (cardinal_separated_cost_integral_le (d := d) (D := D) hn lam hT)
    ((cardinal_separated_cost_integral_le (D := D) hn lam (le_max_left 1 L)).trans hsmall)
  bound

include hlam in
/-- Actual positive representation of E_T minus E_(max(1,L)), with
symmetric marks and the true permutation-averaged packet factors. -/
theorem integrated_cardinal_band_separated_exact
    (L : ℝ) {T : ℝ} (hT : 1 ≤ T) (U : DesignSample d n) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam (max 1 L) U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
        ∂cardinalBandMeasure d n L T := by
  have hm : Measurable (fun z =>
      cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β') :=
    ((((Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _ (fun l _ => cardinal_separated_factor_measurable lam l (U (τ l))))).div_const _ : Measurable fun z => cardinalSeparatedSymmetricFactor lam z U)).comp measurable_snd).mul
      (cardinal_band_amplitude_measurable ..)
  have hiT  := cardinal_separated_symmetric_entry_integrable lam hT hU β β'
  have hiL : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (true, z) β β') (cardinalSeparatedMeasure d n (max 1 L)) := by
    have hh := (cardinal_separated_symmetric_entry_integrable lam (le_max_left 1 L) hU β β').neg
    change Integrable (fun z => -(cardinalSeparatedSymmetricFactor lam z U *
      cardinalSeparatedAmplitude lam z β β')) _ at hh
    simpa only [cardinalBandAmplitude, ite_true, mul_neg] using hh
  rw [cardinal_band_integral_eq_copies L T hm hiT hiL]
  simp only [cardinalBandAmplitude, Bool.false_eq_true, ite_false, ite_true, mul_neg, integral_neg]
  rw [← integrated_cardinal_symmetric_separated_exact hlam hT hU β β',
    ← integrated_cardinal_symmetric_separated_exact hlam (le_max_left 1 L) hU β β']
  ring

include hL in
theorem spatial_scale_domain_empty_below_one (hL1 : L < 1) : spatialScaleDomain i L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hnn : 0 ≤ spatialScaleLogSum t := by
    apply Finset.sum_nonneg
    bound
  grind [Real.log_neg hL hL1, ht.2]

include i hL in
theorem integrated_cardinal_matrix_below_one_eq_zero (hL1 : L < 1)
    (U : DesignSample d n) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam L U β β' = 0 := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  simp_rw [spatial_scale_domain_empty_below_one _ hL hL1, Measure.restrict_empty, integral_zero_measure]
  exact Finset.sum_const_zero

include hn hL in
theorem integrated_cardinal_matrix_max_one (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam (max 1 L) U β β' = integratedCardinalMatrix lam L U β β' := by
  by_cases hL1 : 1 ≤ L
  · rw [max_eq_right hL1]
  · rw [max_eq_left (not_le.mp hL1).le, integrated_cardinal_matrix_one_eq_zero hn,
      integrated_cardinal_matrix_below_one_eq_zero ⟨0, (by omega)⟩ lam hL (not_le.mp hL1)]
    rfl

end NearlyMinimax
