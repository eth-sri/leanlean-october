module

public import NearlyMinimax.PilotMasking
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.ResponseOperatorEnergy


@[expose] public section

/-! Genuine L² and second-moment bounds for the original model's random
pair-score kernel, using independent pilot second moments only. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

section
variable {Ω : Type*} {d : ℕ}

def pairCovariates (z : Observation d × Observation d) : Covariate d × Covariate d :=
  (z.1.1, z.2.1)

theorem pairCovariates_measurable (d : ℕ) : Measurable (pairCovariates (d := d)) :=
  measurable_fst.fst.prodMk measurable_snd.fst

theorem observationPair_covariates_measurePreserving {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) :
    MeasurePreserving pairCovariates ((observationLaw θ).prod (observationLaw θ))
      ((designLaw θ).prod (designLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact (observationLaw_fst_measurePreserving hθ).prod
    (observationLaw_fst_measurePreserving hθ)

def rawModelPairScore (θ : RegressionParameter d)
    {k : ℕ} (hk : 0 < k) (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel hk) z *
    ⟪c p.1 (pairCovariates z), pairScoreOperator θ.variance z.1.2 z.2.2
      (c p.2 (pairCovariates z))⟫

theorem observationPairScoreOperator_measurable_apply (V : ℝ) :
    Measurable (fun z : (Observation d × Observation d) × PairVector =>
      pairScoreOperator V z.1.1.2 z.1.2.2 z.2) := by
  have hv : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      pairResponseVector z.1.1.2 z.1.2.2) :=
    pairResponseVector_continuous.comp
      (continuous_fst.fst.snd.prodMk continuous_fst.snd.snd)
  have hi : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫) := hv.inner continuous_snd
  exact ((hi.smul hv).sub ((pairNoiseOperator.continuous.comp continuous_snd).const_smul V)).measurable

end

section
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (θ : RegressionParameter d) {k : ℕ} (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
include hmc

theorem pilotOnObservations_measurable :
    Measurable (fun z : Ω × (Observation d × Observation d) => c z.1 (pairCovariates z.2)) :=
  hmc.comp (measurable_fst.prodMk ((pairCovariates_measurable d).comp measurable_snd))

theorem rawModelPairScore_measurable :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairScore θ hk c z.1 z.2) := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun z => pairScoreOperator θ.variance z.1.2 z.2.2)
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply θ.variance)
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

theorem rawModelPairScore_memLp :
    MemLp (fun z => rawModelPairScore θ hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (c := fun x z => c x (pairCovariates z))
    (A := fun z => pairScoreOperator θ.variance z.1.2 z.2.2)
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel hk)
      (regularObservationLabel_measurable hk))
  · simp [sameLabelKernel]
  · exact regularResponseOperatorEnergy_integrable hθ hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairScore_energy_le :
    (∫ z, rawModelPairScore θ hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (responseOperatorEnergyBound C * (C.densityUpper / k ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel hk)
      (regularObservationLabel_measurable hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (regularResponseOperatorEnergy_integrable hθ hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  exact he.trans (mul_le_mul_of_nonneg_left (regularResponseOperatorEnergy_le hθ hk)
    (sq_nonneg L))

end NearlyMinimax
