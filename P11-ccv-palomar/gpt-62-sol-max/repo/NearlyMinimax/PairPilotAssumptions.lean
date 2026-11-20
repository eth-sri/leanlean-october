module

public import NearlyMinimax.PairEvaluation
public import NearlyMinimax.PairPilotMean
public import NearlyMinimax.PilotTotalMoments
public import NearlyMinimax.FieldPairMoments


@[expose] public section

/-! Primitive assumptions and their actual-law consequences for the paper's
independent pilots. The conditions contain no pair-risk conclusion. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem regularPairDesignMeasure_ae_of_supported {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    {P : CovariatePair d → Prop}
    (hp : ∀ᵐ w ∂designPairLaw θ,
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → P w) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, P w := by
  change ∀ᵐ w ∂ENNReal.ofReal ((k : ℝ) ^ d) •
    (designPairLaw θ).restrict
      {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}, P w
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))).2
  filter_upwards [hp] with w hw hs
  apply hw
  have hs' : regularGridCell k hk w.1 = regularGridCell k hk w.2 := hs
  simp [sameLabelKernel, hs']

structure PairPilotAssumptions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (Cp W lam : ℝ) : Prop where
  constantNonnegative : 0 ≤ Cp
  budgetNonnegative : 0 ≤ W
  barMeasurable : Measurable bar
  noiseMeasurable : Measurable (fun z : Ω × (CovariatePair d) => η z.1 z.2)
  barBound : ∀ᵐ w ∂designPairLaw θ,
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp
  noiseSection : ∀ᵐ w ∂designPairLaw θ,
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => η x w) 2 μ
  noiseEnergy : ∀ᵐ w ∂designPairLaw θ,
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ Cp * W
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (CovariatePair d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : CovariatePair d → PairVector)
variable (η : Ω → CovariatePair d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hp

theorem pairPilotCoefficient_measurable :
    Measurable (fun z : Ω × (CovariatePair d) => pairPilotCoefficient bar η z.1 z.2) :=
  (hp.barMeasurable.comp measurable_snd).add hp.noiseMeasurable

theorem pairPilotCoefficient_sections :
    ∀ᵐ w ∂designPairLaw θ,
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => pairPilotCoefficient bar η x w) 2 μ := by
  filter_upwards [hp.noiseSection] with w hw hs
  solve_by_elim [PilotFields.pilot_coefficient_memLp_two]

theorem pairPilotCoefficient_energy :
    ∀ᵐ w ∂designPairLaw θ,
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, ‖pairPilotCoefficient bar η x w‖ ^ 2 ∂μ) ≤ 2 * Cp ^ 2 + 2 * Cp * W := by
  filter_upwards [hp.noiseSection, hp.barBound, hp.noiseEnergy] with w hs hb he hq
  simpa only [pairPilotCoefficient, mul_assoc] using
    PilotFields.pilot_coefficient_second_moment_le (bar w) (hs hq) (hb hq) (he hq)

include C hθ

private theorem pairPilotKernel_moments {A : PairOperator d} {B : ℝ}
    (hmA : Measurable (fun z : ObservationPair d × PairVector => A z.1 z.2))
    (hiA : Integrable (fun z => observationPairMask k hk z * ‖A z‖ ^ 2) (observationPairLaw θ))
    (hA : (∫ z, observationPairMask k hk z * ‖A z‖ ^ 2 ∂observationPairLaw θ) ≤ B) :
    PairKernelMoments (μ.prod μ) θ (pairEvaluationKernel k hk A (pairPilotCoefficient bar η))
      ((2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * B) :=
  pairEvaluationKernel_moments μ C θ hθ k hk (c := pairPilotCoefficient bar η) (A := A) (B := B)
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp) hmA hiA hA

theorem pairPilotScoreKernel_moments :
    PairKernelMoments (μ.prod μ) θ (pairPilotScoreKernel θ k hk bar η)
      ((2 * Cp ^ 2 + 2 * Cp * W)^2 * (responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ)^d))) := by
  have h := regularResponseOperatorEnergy_moments C θ hθ k hk
  exact pairPilotKernel_moments μ C θ hθ k hk bar η Cp W lam hp (A := observationScoreOperator θ.variance)
    (observationPairScoreOperator_measurable_apply θ.variance)
    h.1 h.2

theorem pairPilotNoiseKernel_moments :
    PairKernelMoments (μ.prod μ) θ (pairPilotNoiseKernel k hk bar η)
      ((2 * Cp ^ 2 + 2 * Cp * W)^2 * (4 * (C.densityUpper / (k : ℝ)^d))) :=
  pairPilotKernel_moments μ C θ hθ k hk bar η Cp W lam hp (A := observationNoiseOperator)
    (observationPairNoiseOperator_measurable_apply d)
    (observationPairNoiseOperator_energy_integrable C θ hθ k hk) (observationPairNoiseOperator_energy_le C θ hθ k hk)

theorem pairPilotAssumptions_meanConditions :
    PairPilotMeanConditions θ k hk μ bar η Cp lam := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  let := observationLaw_isProbability C θ hθ
  have hs := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection
  have he := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy
  refine ⟨hp.barMeasurable, regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound,
    hp.noiseMeasurable, ?_, hp.noiseCentered, hp.lamNonnegative, hp.linearTest, ?_, ?_⟩
  · exact (PilotFields.pilot_joint_section_moments hp.noiseMeasurable hs he).1
  · exact ((pairPilotScoreKernel_moments μ C θ hθ k hk bar η Cp W lam hp).2.1.integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae
  · exact ((pairPilotNoiseKernel_moments μ C θ hθ k hk bar η Cp W lam hp).2.1.integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae


end
end NearlyMinimax
