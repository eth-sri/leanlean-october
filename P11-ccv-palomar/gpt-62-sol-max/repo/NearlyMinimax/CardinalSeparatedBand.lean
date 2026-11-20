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
  ∑ b : Bool, (cardinalSeparatedMeasure d n (if b then max 1 L else T)).map (fun z => (b, z))

def cardinalBandAmplitude {d n D : ℕ} (lam : ℝ) (z : CardinalBandMark d n)
    (β β' : HighFrameIndex d D) : ℝ :=
  if z.1 then -cardinalSeparatedAmplitude lam z.2 β β' else cardinalSeparatedAmplitude lam z.2 β β'

def cardinalBandFactor {d n : ℕ} (lam : ℝ) (z : CardinalBandMark d n)
    (l : Fin n) (x : Covariate d) : ℝ := cardinalSeparatedFactor lam z.2 l x

section
variable (d n : ℕ)

theorem cardinal_band_mark_standardBorel : StandardBorelSpace (CardinalBandMark d n) := by
  letI := cardinal_separated_mark_standardBorel d n
  infer_instance

theorem cardinal_band_measure_finite (L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalBandMeasure d n L T) := by
  letI := cardinal_separated_measure_finite d n hT
  letI := cardinal_separated_measure_finite d n (le_max_left 1 L)
  unfold cardinalBandMeasure
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  infer_instance

end

theorem cardinal_band_amplitude_measurable {d n D : ℕ} (lam : ℝ) (β β' : HighFrameIndex d D) :
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

theorem cardinal_band_factor_abs_le_one (z : CardinalBandMark d n)
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) : |cardinalBandFactor lam z l x| ≤ 1 :=
  by apply cardinal_separated_factor_abs_le_one <;> assumption

end

private theorem cardinal_band_moments (L T : ℝ)
    {f : CardinalBandMark d n → ℝ} (hf : Measurable f)
    (hT : Integrable (fun z => f (false, z)) (cardinalSeparatedMeasure d n T))
    (hL : Integrable (fun z => f (true, z)) (cardinalSeparatedMeasure d n (max 1 L))) :
    Integrable f (cardinalBandMeasure d n L T) ∧
    (∫ z, f z ∂cardinalBandMeasure d n L T) =
      (∫ z, f (true, z) ∂cardinalSeparatedMeasure d n (max 1 L)) +
        (∫ z, f (false, z) ∂cardinalSeparatedMeasure d n T) := by
  have h := finite_map_mixture_moments (fun b (z : CardinalSeparatedMark d n) => (b,z))
    (fun b => measurable_const.prodMk measurable_id)
    (fun b : Bool => cardinalSeparatedMeasure d n (if b then max 1 L else T)) hf
    (fun b => by cases b <;> assumption)
  exact ⟨h.1, by simpa only [cardinalBandMeasure, Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false] using h.2⟩

end

section
variable {d n D : ℕ}

theorem cardinal_band_cost_eq (lam : ℝ) (z : CardinalBandMark d n) :
    separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z =
      separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z.2 := by
  unfold separatedMatrixCost cardinalBandAmplitude
  cases z.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg]

private theorem cardinal_band_cost_moments (lam L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    let cost := separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)
    Integrable cost (cardinalBandMeasure d n L T) ∧
    (∫ z, cost z ∂cardinalBandMeasure d n L T) =
      (∫ z, cost (true, z) ∂cardinalSeparatedMeasure d n (max 1 L)) +
      (∫ z, cost (false, z) ∂cardinalSeparatedMeasure d n T) :=
  cardinal_band_moments L T
    (separatedMatrixCost_measurable (cardinal_band_amplitude_measurable (d := d) (n := n) (D := D) lam))
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam hT)
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam (le_max_left 1 L))

theorem cardinal_band_cost_integrable (lam L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalBandAmplitude (D := D) lam)) (cardinalBandMeasure d n L T) :=
  (cardinal_band_cost_moments (d := d) (n := n) (D := D) lam L hT).1

theorem cardinal_band_cost_integral_le (hn : 2 ≤ n) (lam L : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ z, separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z ∂cardinalBandMeasure d n L T) ≤
      2 * cardinalSeparatedCostBound d n lam T := by
  rw [(cardinal_band_cost_moments lam L hT).2, two_mul]
  simp_rw [cardinal_band_cost_eq]
  exact add_le_add ((cardinal_separated_cost_integral_le hn lam (le_max_left 1 L)).trans
    (cardinalSeparatedCostBound_mono lam (le_max_left 1 L) (max_le hT hLT)))
    (cardinal_separated_cost_integral_le hn lam hT)

end

theorem cardinal_separated_symmetric_factor_measurable {d n : ℕ} (lam : ℝ) (U : Fin n → Covariate d) :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedSymmetricFactor lam z U) := by
  exact (Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _
      (fun l _ => cardinal_separated_factor_measurable lam l (U (τ l))))).div_const _

/-- Actual positive representation of E_T minus E_(max(1,L)), with
symmetric marks and the true permutation-averaged packet factors. -/
theorem integrated_cardinal_band_separated_exact {d n D : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    (L : ℝ) {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
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
    simpa only [cardinalBandAmplitude, Bool.false_eq_true, ite_false] using
      cardinal_separated_symmetric_entry_integrable lam hT U hU β β'
  have hiL : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (true, z) β β') (cardinalSeparatedMeasure d n (max 1 L)) := by
    have hh := (cardinal_separated_symmetric_entry_integrable lam (le_max_left 1 L) U hU β β').neg
    change Integrable (fun z => -(cardinalSeparatedSymmetricFactor lam z U *
      cardinalSeparatedAmplitude lam z β β')) (cardinalSeparatedMeasure d n (max 1 L)) at hh
    simpa only [cardinalBandAmplitude, ite_true, mul_neg] using hh
  rw [(cardinal_band_moments L T hm hiT hiL).2]
  simp only [cardinalBandAmplitude, Bool.false_eq_true, ite_false, ite_true, mul_neg, integral_neg]
  rw [← integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β',
    ← integrated_cardinal_symmetric_separated_exact lam hlam (le_max_left 1 L) U hU β β']
  ring

theorem spatial_scale_domain_empty_below_one {n : ℕ} (i : Fin n) {L : ℝ}
    (hL : 0 < L) (hL1 : L < 1) : spatialScaleDomain i L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hnn : 0 ≤ spatialScaleLogSum i t := by
    unfold spatialScaleLogSum
    apply Finset.sum_nonneg
    grind [Real.log_nonneg]
  have hl := Real.log_neg hL hL1
  have hc : spatialScaleLogSum i t ≤ 2 * Real.log L := ht.2
  linarith

section
variable {d n D : ℕ}

theorem integrated_cardinal_matrix_below_one_eq_zero (lam : ℝ) {L : ℝ} (hL : 0 < L) (hL1 : L < 1)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam L U β β' = 0 := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  simp [spatial_scale_domain_empty_below_one _ hL hL1, Measure.restrict_empty, integral_zero_measure]

section
variable (hn : 2 ≤ n)
    (lam : ℝ)
include hn

theorem integrated_cardinal_matrix_max_one {L : ℝ} (hL : 0 < L) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam (max 1 L) U β β' = integratedCardinalMatrix lam L U β β' := by
  by_cases hL1 : 1 ≤ L
  · simp_all
  · have hn0 : 0 < n := by omega
    simp [max_eq_left (not_le.mp hL1).le, integrated_cardinal_matrix_one_eq_zero hn, integrated_cardinal_matrix_below_one_eq_zero lam hL (not_le.mp hL1)]

/-- Positive separated representation of every actual band with 0<L≤T,
including the zero convention below scale one. -/
theorem integrated_cardinal_actual_band_separated_exact (hlam : 0 ≤ lam) {L T : ℝ} (hL : 0 < L) (hT : 1 ≤ T)
    (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
        ∂cardinalBandMeasure d n L T := by
  rw [← integrated_cardinal_matrix_max_one hn lam hL U β β']
  apply integrated_cardinal_band_separated_exact <;> assumption

end

end

end NearlyMinimax
