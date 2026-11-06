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

abbrev CardinalBandMark d n := Bool × CardinalSeparatedMark d n

def cardinalBandMeasure (d n : ℕ) (L T : ℝ) : Measure (CardinalBandMark d n) :=
  Measure.map (fun z => (false, z)) (cardinalSeparatedMeasure d n T) +
    Measure.map (fun z => (true, z)) (cardinalSeparatedMeasure d n (max 1 L))

def cardinalBandAmplitude {d n D } lam (z : CardinalBandMark d n)
    (β β' : HighFrameIndex d D)  :=
  if z.1 then -cardinalSeparatedAmplitude lam z.2 β β' else cardinalSeparatedAmplitude lam z.2 β β'

def cardinalBandFactor {d n } lam (z : CardinalBandMark d n)
    l x  := cardinalSeparatedFactor lam z.2 l x

section
variable (d n : ℕ)

theorem cardinal_band_mark_standardBorel  : StandardBorelSpace (CardinalBandMark d n) := by
  letI := cardinal_separated_mark_standardBorel d n
  infer_instance

theorem cardinal_band_measure_finite  L {T } (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalBandMeasure d n L T) := by
  letI := cardinal_separated_measure_finite d n hT
  letI := cardinal_separated_measure_finite d n (le_max_left 1 L)
  unfold cardinalBandMeasure
  infer_instance
end


theorem cardinal_band_amplitude_measurable {d n D } lam (β β' : HighFrameIndex d D) :
    Measurable (fun z : CardinalBandMark d n => cardinalBandAmplitude lam z β β') := by
  unfold cardinalBandAmplitude
  apply Measurable.ite
  · exact measurable_fst (measurableSet_singleton true)
  · exact ((cardinal_separated_amplitude_measurable lam β β').comp measurable_snd).neg
  · exact (cardinal_separated_amplitude_measurable lam β β').comp measurable_snd

section
variable {d n : ℕ}

section
variable (lam : ℝ)

theorem cardinal_band_factor_measurable   l x :
    Measurable (fun z : CardinalBandMark d n => cardinalBandFactor lam z l x) :=
  (cardinal_separated_factor_measurable lam l x).comp measurable_snd

theorem cardinal_band_factor_abs_le_one   z
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) : |cardinalBandFactor lam z l x| ≤ 1 :=
  cardinal_separated_factor_abs_le_one lam z.2 l x hx
end


section
variable (L T : ℝ) (f : CardinalBandMark d n → ℝ) (hf : Measurable f) (hT : Integrable (fun z => f (false, z)) (cardinalSeparatedMeasure d n T)) (hL : Integrable (fun z => f (true, z)) (cardinalSeparatedMeasure d n (max 1 L)))
include hf hT hL

theorem cardinal_band_integrable_of_copies   :
    Integrable f (cardinalBandMeasure d n L T) := by
  unfold cardinalBandMeasure
  apply integrable_add_measure.mpr
  constructor
  · exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_const.prodMk measurable_id).aemeasurable).mpr hT
  · exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_const.prodMk measurable_id).aemeasurable).mpr hL

theorem cardinal_band_integral_eq_copies   :
    (∫ z, f z ∂cardinalBandMeasure d n L T) =
      (∫ z, f (false, z) ∂cardinalSeparatedMeasure d n T) +
        (∫ z, f (true, z) ∂cardinalSeparatedMeasure d n (max 1 L)) := by
  have hmF : Measurable (fun z : CardinalSeparatedMark d n => (false, z)) := by fun_prop
  have hmL : Measurable (fun z : CardinalSeparatedMark d n => (true, z)) := by fun_prop
  have hiF  :=
    (integrable_map_measure hf.aestronglyMeasurable hmF.aemeasurable).mpr hT
  have hiL  :=
    (integrable_map_measure hf.aestronglyMeasurable hmL.aemeasurable).mpr hL
  unfold cardinalBandMeasure
  rw [integral_add_measure hiF hiL,
    integral_map hmF.aemeasurable hf.aestronglyMeasurable,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable]
end

end


section
variable {d n D : ℕ}

theorem cardinal_band_cost_eq  lam (z : CardinalBandMark d n) :
    separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z =
      separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z.2 := by
  unfold separatedMatrixCost cardinalBandAmplitude
  cases z.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg]

theorem cardinal_band_cost_integrable  lam L {T } (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalBandAmplitude (D := D) lam)) (cardinalBandMeasure d n L T) := by
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs))
  simp_all [cardinal_band_integrable_of_copies, cardinal_band_cost_eq, cardinal_separated_cost_integrable]

theorem cardinal_band_cost_integral_le  (hn : 2 ≤ n) lam L
    {T } (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ z, separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z ∂cardinalBandMeasure d n L T) ≤
      2 * n * (1024 * |lam| * d ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs))
  rw [cardinal_band_integral_eq_copies L T _ hm
    (by solve_by_elim [cardinal_separated_cost_integrable])
    (by simp_all [cardinal_band_cost_eq, cardinal_separated_cost_integrable])]
  simp_rw [cardinal_band_cost_eq]
  have hmax : max 1 L ≤ T := max_le hT hLT
  have hp : 0 < max 1 L := lt_of_lt_of_le (by norm_num) (le_max_left 1 L)
  have hlog : 1 + Real.log (max 1 L) ≤ 1 + Real.log T := add_le_add le_rfl (Real.log_le_log hp hmax)
  have hsmall : (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * (max 1 L) ^ 2 *
      (1 + Real.log (max 1 L)) ^ (n - 2) ≤
      (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
    have hlogn : 0 ≤ 1 + Real.log (max 1 L) :=
      add_nonneg (by norm_num) (Real.log_nonneg (le_max_left 1 L))
    gcongr
  have h := add_le_add (cardinal_separated_cost_integral_le (d := d) (D := D) hn lam hT)
    ((cardinal_separated_cost_integral_le (d := d) (D := D) hn lam (le_max_left 1 L)).trans hsmall)
  convert h using 1 <;> ring
end


theorem cardinal_separated_symmetric_factor_measurable {d n } lam U :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedSymmetricFactor lam z U) := (Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _
    (fun l _ => cardinal_separated_factor_measurable lam l (U (τ l))))).div_const _

/-- Actual positive representation of E_T minus E_(max(1,L)), with
symmetric marks and the true permutation-averaged packet factors. -/
theorem integrated_cardinal_band_separated_exact {d n D } lam (hlam : 0 ≤ lam)
    L {T } (hT : 1 ≤ T) U (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam (max 1 L) U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
        ∂cardinalBandMeasure d n L T := by
  have hm : Measurable (fun z : CardinalBandMark d n =>
      cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β') :=
    ((cardinal_separated_symmetric_factor_measurable lam U).comp measurable_snd).mul
      (cardinal_band_amplitude_measurable lam β β')
  have hiT : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (false, z) β β') (cardinalSeparatedMeasure d n T) := by
    solve_by_elim [cardinal_separated_symmetric_entry_integrable]
  have hiL : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (true, z) β β') (cardinalSeparatedMeasure d n (max 1 L)) := by
    have hh := (cardinal_separated_symmetric_entry_integrable lam (le_max_left 1 L) U hU β β').neg
    change Integrable (fun z => -(cardinalSeparatedSymmetricFactor lam z U *
      cardinalSeparatedAmplitude lam z β β')) (cardinalSeparatedMeasure d n (max 1 L)) at hh
    simpa only [cardinalBandAmplitude, ite_true, mul_neg] using hh
  rw [cardinal_band_integral_eq_copies L T _ hm hiT hiL]
  simp only [cardinalBandAmplitude, Bool.false_eq_true, ite_false, ite_true, mul_neg, integral_neg]
  rw [← integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β',
    ← integrated_cardinal_symmetric_separated_exact lam hlam (le_max_left 1 L) U hU β β']
  ring

theorem spatial_scale_domain_empty_below_one {n } (i : Fin n) {L }
    (hL : 0 < L) (hL1 : L < 1) : spatialScaleDomain i L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hnn : 0 ≤ spatialScaleLogSum i t := by
    unfold spatialScaleLogSum
    simp_all [Finset.sum_nonneg, Real.log_nonneg]
  have hl := Real.log_neg hL hL1
  have hc : spatialScaleLogSum i t ≤ 2 * Real.log L := ht.2
  linarith

section
variable {d n D : ℕ}

theorem integrated_cardinal_matrix_below_one_eq_zero 
    (i : Fin n) lam {L } (hL : 0 < L) (hL1 : L < 1)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam L U β β' = 0 := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  simp_rw [spatial_scale_domain_empty_below_one _ hL hL1, Measure.restrict_empty, integral_zero_measure]
  exact Finset.sum_const_zero

section
variable (hn : 2 ≤ n) (lam : ℝ)
include hn

theorem integrated_cardinal_matrix_max_one   {L } (hL : 0 < L) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam (max 1 L) U β β' = integratedCardinalMatrix lam L U β β' := by
  by_cases hL1 : 1 ≤ L
  · rw [max_eq_right hL1]
  · have hn0 : 0 < n := by omega
    rw [max_eq_left (not_le.mp hL1).le, integrated_cardinal_matrix_one_eq_zero hn,
      integrated_cardinal_matrix_below_one_eq_zero ⟨0, hn0⟩ lam hL (not_le.mp hL1)]
    rfl

/-- Positive separated representation of every actual band with 0<L≤T,
including the zero convention below scale one. -/
theorem integrated_cardinal_actual_band_separated_exact   (hlam : 0 ≤ lam) {L T } (hL : 0 < L) (hT : 1 ≤ T)
    U (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
        ∂cardinalBandMeasure d n L T := by
  rw [← integrated_cardinal_matrix_max_one hn lam hL U β β']
  exact integrated_cardinal_band_separated_exact lam hlam L hT U hU β β'
end

end


end NearlyMinimax
