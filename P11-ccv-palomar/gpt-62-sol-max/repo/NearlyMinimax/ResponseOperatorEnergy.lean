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

def localizedResponseOperatorEnergy (V : ℝ) (z : E × E) : ℝ :=
  sameLabelKernel label z * ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2

theorem localizedResponseOperatorEnergy_moments (V B4 : ℝ)
    (hr4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ i : I, (∫ x, (label ⁻¹' {i}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      B4 * μ.real (label ⁻¹' {i})) :
    Integrable (localizedResponseOperatorEnergy label r V) (μ.prod μ) ∧
    (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      (12 * B4 + 6 + 8 * V ^ 2) * ∑ i : I, μ.real (label ⁻¹' {i}) ^ 2 := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG : Integrable G (μ.prod μ) := labelLocalizedKernel_integrable μ label hlabel _ hr4
  have hGs : Integrable (fun z : E × E => G z.swap) (μ.prod μ) := integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hdom := ((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul (6 + 8 * V ^ 2))
  have hb (z : E × E) : localizedResponseOperatorEnergy label r V z ≤
      6 * G z + 6 * G z.swap + (6 + 8 * V ^ 2) * sameLabelKernel label z := by
    by_cases he : label z.1 = label z.2
    · simp only [localizedResponseOperatorEnergy, sameLabelKernel, G, labelLocalizedKernel,
        Prod.fst_swap, Prod.snd_swap, if_pos he, if_pos he.symm, one_mul, mul_one]
      linarith [pairScoreOperator_norm_sq_le V (r z.1) (r z.2)]
    · simp [localizedResponseOperatorEnergy, sameLabelKernel, G, labelLocalizedKernel, he, Ne.symm he]
  have hm : Measurable (localizedResponseOperatorEnergy label r V) :=
    (sameLabelKernel_measurable label hlabel).mul
      (((pairScoreOperator_continuous V).measurable.comp (hmr.prodMap hmr)).norm.pow_const 2)
  have hi := hdom.mono' hm.aestronglyMeasurable (.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by unfold sameLabelKernel; positivity) (sq_nonneg _))]
    exact hb z)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hdom hb
  have hupper : (∫ z, G z ∂μ.prod μ) ≤ _ := labelLocalizedKernel_integral_le μ label hlabel _ hr4 B4 hloc
  have hsplit := integral_add ((hG.const_mul 6).add (hGs.const_mul 6)) (hq.const_mul (6 + 8 * V ^ 2))
  have hsplit' := integral_add (hG.const_mul 6) (hGs.const_mul 6)
  simp only [Pi.add_apply] at h hsplit hsplit'
  rw [hsplit, hsplit'] at h
  simp only [integral_const_mul, integral_prod_swap G,
    sameLabelKernel_integral μ label hlabel] at h
  linarith

end Partition

def responseOperatorEnergyBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2

section
variable {d : ℕ} (C : ModelConstants d)

theorem responseOperatorEnergyBound_pos :
    0 < responseOperatorEnergyBound C := by
  have h4 := responseFourthBound_pos C
  unfold responseOperatorEnergyBound
  positivity

theorem regularResponseOperatorEnergy_moments
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance) (observationPairLaw θ) ∧
    (∫ z, localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance z ∂observationPairLaw θ) ≤
      responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  obtain ⟨hi, hb⟩ := localizedResponseOperatorEnergy_moments (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
    (responseFourthBound C) (observationLaw_response_fourth_integrable C θ hθ) (by
      intro i
      rw [regularObservationLabel_mass C θ hθ k hk i, regularObservationLabel_fiber k hk i]
      exact observationLaw_localized_fourth_integral_le C θ hθ _
        ((measurableSet_singleton i).preimage (regular_grid_cell_measurable k hk)))
  simp_rw [regularObservationLabel_mass C θ hθ k hk] at hb
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVup := hθ.2.2.2.2.2.2.1
  have hvsq := pow_le_pow_left₀ hV0 hVup 2
  have hmass : 0 ≤ regularGridCollisionMass θ k hk := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change _ ≤ (12 * responseFourthBound C + 6 + 8 * θ.variance ^ 2) *
    regularGridCollisionMass θ k hk at hb
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ responseOperatorEnergyBound C * regularGridCollisionMass θ k hk := by
      apply mul_le_mul_of_nonneg_right _ hmass
      unfold responseOperatorEnergyBound
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk)
      (responseOperatorEnergyBound_pos C).le

end

end NearlyMinimax
