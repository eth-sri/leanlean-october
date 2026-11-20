module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PairWindowModel

@[expose] public section

/-! Localized fourth-moment control of the actual response operators. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Partition
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (label : E → I) (hlabel : Measurable label)
  (r : E → ℝ) (hmr : Measurable r)
include hlabel hmr

variable (V B4 : ℝ) (hr4 : Integrable (fun x => r x ^ 4) μ)

def localizedResponseOperatorEnergy (z : E × E) : ℝ :=
  sameLabelKernel label z * ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2

include hr4 in
theorem localizedResponseOperatorEnergy_integrable :
    Integrable (localizedResponseOperatorEnergy label r V) (μ.prod μ) := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG  := labelLocalizedKernel_integrable μ label hlabel hr4
  have hGs  :=
    integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hi : Integrable (fun z =>
      6 * G z + 6 * G z.swap + (6 + 8 * V ^ 2) * sameLabelKernel label z) (μ.prod μ) :=
    ((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _)
  have hm : Measurable (localizedResponseOperatorEnergy label r V) := by
    apply (sameLabelKernel_measurable label hlabel).mul
    exact (((((InnerProductSpace.rankOne ℝ).continuous.comp pairResponseVector_continuous).clm_apply pairResponseVector_continuous |>.sub continuous_const).measurable.comp
      ((hmr.comp measurable_fst).prodMk (hmr.comp measurable_snd))).norm.pow_const 2)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by unfold sameLabelKernel; split_ifs <;> norm_num) (sq_nonneg _))]
  by_cases he : label z.1 = label z.2
  · simpa only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
      labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap,  one_mul, mul_one] using
      (show ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2 ≤
        6 * r z.2 ^ 4 + 6 * r z.1 ^ 4 + (6 + 8 * V ^ 2) by nlinarith [(pairScoreOperator_norm_sq_le V (r z.1) (r z.2))])
  · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
      he, Ne.symm he]

include hr4 in
theorem localizedResponseOperatorEnergy_integral_le
    (hloc : ∀ i, (∫ x, (label ⁻¹' {i}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      B4 * μ.real (label ⁻¹' {i})) :
    (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      (12 * B4 + 6 + 8 * V ^ 2) * ∑ i, μ.real (label ⁻¹' {i}) ^ 2 := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG  := labelLocalizedKernel_integrable μ label hlabel hr4
  have hGs : Integrable (fun z => G z.swap) (μ.prod μ) :=
    integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hupper := labelLocalizedKernel_integral_le μ label hlabel hr4 hloc
  have hb : (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      ∫ z, 6 * G z + 6 * G z.swap +
        (6 + 8 * V ^ 2) * sameLabelKernel label z ∂μ.prod μ := by
    apply integral_mono (localizedResponseOperatorEnergy_integrable μ label hlabel r hmr V hr4)
      (((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _))
    intro z
    simp
    by_cases he : label z.1 = label z.2
    · simp only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
        labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul]
      nlinarith [(pairScoreOperator_norm_sq_le V (r z.1) (r z.2))]
    · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
        he, Ne.symm he]
  have ha := integral_add ((hG.const_mul 6).add (hGs.const_mul 6)) (hq.const_mul (6 + 8 * V ^ 2))
  have ha' := integral_add (hG.const_mul 6) (hGs.const_mul 6)
  simp at ha ha'
  rw [ha, ha', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_swap G, sameLabelKernel_integral μ label hlabel] at hb
  nlinarith

end Partition

section
variable {d : ℕ} (C : ModelConstants d)

def responseOperatorEnergyBound : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2

theorem responseOperatorEnergyBound_pos :
    0 < responseOperatorEnergyBound C := by
  have h4 := responseFourthBound_pos C
  unfold responseOperatorEnergyBound
  positivity

end

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ}
    (hk : 0 < k)
include hθ

theorem regularResponseOperatorEnergy_integrable :
    Integrable (localizedResponseOperatorEnergy (regularObservationLabel hk)
      Prod.snd θ.variance) ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact localizedResponseOperatorEnergy_integrable (observationLaw θ) _
    (regularObservationLabel_measurable hk) Prod.snd measurable_snd θ.variance
      (observationLaw_response_fourth_integrable hθ)

theorem regularResponseOperatorEnergy_le :
    (∫ z, localizedResponseOperatorEnergy (regularObservationLabel hk)
      Prod.snd θ.variance z ∂(observationLaw θ).prod (observationLaw θ)) ≤
      responseOperatorEnergyBound C * (C.densityUpper / k ^ d) := by
  let := observationLaw_isProbability C θ hθ
  have hb := localizedResponseOperatorEnergy_integral_le (observationLaw θ) _
    (regularObservationLabel_measurable hk) Prod.snd measurable_snd θ.variance
    (responseFourthBound C) (observationLaw_response_fourth_integrable hθ) (by
      intro i
      rw [regularObservationLabel_mass hθ hk i, regularObservationLabel_fiber hk i]
      exact observationLaw_localized_fourth_integral_le hθ
        ((measurableSet_singleton i).preimage (regular_grid_cell_measurable k hk)))
  simp_rw [regularObservationLabel_mass hθ hk] at hb
  have hV0  := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVup := hθ.2.2.2.2.2.2.1
  apply hb.trans
  calc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      unfold responseOperatorEnergyBound
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper hθ hk)
      (responseOperatorEnergyBound_pos C).le

end NearlyMinimax
