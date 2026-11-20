module

public import NearlyMinimax.PairEvaluation


@[expose] public section

/-! The same actual-law pilot-energy argument for the pair denominator. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

section
variable {Ω : Type*} {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ)
    {k : ℕ} (hk : 0 < k)

include hθ in
theorem observationPairNoiseOperator_energy_integrable :
    Integrable (fun z =>
      sameLabelKernel (regularObservationLabel hk) z * ‖pairNoiseOperator‖ ^ 2)
      ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact ((sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable hk)).integrable (by norm_num)).mul_const _

include hθ in
theorem observationPairNoiseOperator_energy_le :
    (∫ z,
      sameLabelKernel (regularObservationLabel hk) z * ‖pairNoiseOperator‖ ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤ 4 * (C.densityUpper / k ^ d) := by
  let := observationLaw_isProbability C θ hθ
  rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable hk)]
  simp_rw [regularObservationLabel_mass hθ hk]
  have hq : 0 ≤ regularGridCollisionMass θ hk := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left (by
    have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2
    exact h) hq).trans (by have h := regularGridCollisionMass_upper hθ hk; linarith)

def rawModelPairNoise
    (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel hk) z *
    ⟪c p.1 (pairCovariates z), pairNoiseOperator (c p.2 (pairCovariates z))⟫

theorem rawModelPairNoise_measurable [MeasurableSpace Ω] {d k : ℕ} (hk : 0 < k) {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairNoise hk c z.1 z.2) := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ => pairNoiseOperator)
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel hk)
      (regularObservationLabel_measurable hk))

end

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} [IsProbabilityMeasure π] {d : ℕ}
    {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ} (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ), sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hL : 0 ≤ L)
    (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ), sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L)
include hE hL hc hmc hθ

theorem rawModelPairNoise_memLp :
    MemLp (fun z => rawModelPairNoise hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ => pairNoiseOperator)
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel hk)
      (regularObservationLabel_measurable hk))
  · simp [sameLabelKernel]
  · exact observationPairNoiseOperator_energy_integrable hθ hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairNoise_energy_le :
    (∫ z, rawModelPairNoise hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (4 * (C.densityUpper / k ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel hk)
      (regularObservationLabel_measurable hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (observationPairNoiseOperator_energy_integrable hθ hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  exact he.trans (mul_le_mul_of_nonneg_left (observationPairNoiseOperator_energy_le hθ hk)
    (sq_nonneg L))

end NearlyMinimax
