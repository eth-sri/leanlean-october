module

public import NearlyMinimax.MaskedPilotKernel
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

def pairCovariates {d : ℕ} (z : ObservationPair d) : CovariatePair d :=
  (z.1.1, z.2.1)

theorem pairCovariates_measurable (d : ℕ) : Measurable (pairCovariates (d := d)) :=
  measurable_fst.fst.prodMk measurable_snd.fst

theorem observationPair_covariates_measurePreserving {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving pairCovariates (observationPairLaw θ)
      (designPairLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  exact (observationLaw_fst_measurePreserving C θ hθ).prod
    (observationLaw_fst_measurePreserving C θ hθ)

abbrev PairOperator (d : ℕ) := ObservationPair d → PairVector →L[ℝ] PairVector

abbrev observationScoreOperator {d : ℕ} (V : ℝ) : PairOperator d :=
  fun z => pairScoreOperator V z.1.2 z.2.2

abbrev observationNoiseOperator {d : ℕ} : PairOperator d := fun _ => pairNoiseOperator

abbrev observationPairMask {d : ℕ} (k : ℕ) (hk : 0 < k) : ObservationPair d → ℝ :=
  sameLabelKernel (regularObservationLabel k hk)

def pairEvaluationKernel {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (A : PairOperator d) (c : Ω → CovariatePair d → PairVector) (p : Ω × Ω) (z : ObservationPair d) : ℝ :=
  PilotFields.maskedPilotKernel (fun x z => c x (pairCovariates z)) A (observationPairMask k hk) (p, z)

abbrev rawModelPairNoise {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → CovariatePair d → PairVector) := pairEvaluationKernel k hk observationNoiseOperator c

abbrev coefficientPairNumeratorKernel {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → CovariatePair d → PairVector) := pairEvaluationKernel k hk (observationScoreOperator 0) c

theorem observationPairScoreOperator_measurable_apply {d : ℕ} (V : ℝ) :
    Measurable (fun z : ObservationPair d × PairVector => observationScoreOperator V z.1 z.2) := by
  have hv : Continuous (fun z : (ObservationPair d) × PairVector =>
      pairResponseVector z.1.1.2 z.1.2.2) :=
    pairResponseVector_continuous.comp
      (continuous_fst.fst.snd.prodMk continuous_fst.snd.snd)
  have hi : Continuous (fun z : (ObservationPair d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫) := hv.inner continuous_snd
  have hs : Continuous (fun z : (ObservationPair d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫ • pairResponseVector z.1.1.2 z.1.2.2) := hi.smul hv
  simpa only [pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, starRingEnd_apply, star_trivial, observationScoreOperator,
    Pi.sub_def, Pi.smul_def, Function.comp_def] using
    (hs.sub ((pairNoiseOperator.continuous.comp continuous_snd).const_smul V)).measurable

theorem observationPairNoiseOperator_measurable_apply (d : ℕ) :
    Measurable (fun z : ObservationPair d × PairVector => observationNoiseOperator z.1 z.2) :=
  pairNoiseOperator.continuous.measurable.comp measurable_snd

section
variable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
include hθ

theorem observationPairNoiseOperator_energy_integrable :
    Integrable (fun z : ObservationPair d =>
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2)
      (observationPairLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  exact ((sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk)).integrable (by norm_num)).mul_const _

theorem observationPairNoiseOperator_energy_le :
    (∫ z : ObservationPair d,
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2
      ∂observationPairLaw θ) ≤ 4 * (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable k hk)]
  simp_rw [regularObservationLabel_mass C θ hθ k hk]
  change regularGridCollisionMass θ k hk * ‖pairNoiseOperator‖ ^ 2 ≤ _
  have hq : 0 ≤ regularGridCollisionMass θ k hk := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : ‖pairNoiseOperator‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2
    norm_num at h
    assumption
  calc
    _ ≤ regularGridCollisionMass θ k hk * 4 := mul_le_mul_of_nonneg_left hN hq
    _ ≤ _ := by have h := regularGridCollisionMass_upper C θ hθ k hk; linarith

end

section
variable {Ω : Type*} [MeasurableSpace Ω]

section
variable {d : ℕ}

theorem pilotOnObservations_measurable
    {c : Ω → CovariatePair d → PairVector}
    (hmc : Measurable (fun z : Ω × (CovariatePair d) => c z.1 z.2)) :
    Measurable (fun z : Ω × (ObservationPair d) => c z.1 (pairCovariates z.2)) :=
  hmc.comp (measurable_fst.prodMk ((pairCovariates_measurable d).comp measurable_snd))

theorem pairEvaluationKernel_measurable (k : ℕ) (hk : 0 < k)
    {A : PairOperator d} {c : Ω → CovariatePair d → PairVector}
    (hmc : Measurable (Function.uncurry c)) (hmA : Measurable (fun z : ObservationPair d × PairVector => A z.1 z.2)) :
    Measurable (Function.uncurry (pairEvaluationKernel k hk A c)) :=
  PilotFields.maskedPilotKernel_measurable (c := fun x (z : ObservationPair d) => c x (pairCovariates z))
    (pilotOnObservations_measurable hmc) hmA
    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))

end

def PairKernelMoments {P : Type*} [MeasurableSpace P] {d : ℕ} (π : Measure P)
    (θ : RegressionParameter d) (G : P → ObservationPair d → ℝ) (energy : ℝ) : Prop :=
  Measurable (Function.uncurry G) ∧ MemLp (Function.uncurry G) 2 (π.prod (observationPairLaw θ)) ∧
    (∫ z : P × ObservationPair d, G z.1 z.2 ^ 2 ∂π.prod (observationPairLaw θ)) ≤ energy

/-- Both kernels use the same collision mask and the same pilot moment
hypotheses. Only the operator's energy and measurability differ. -/
theorem pairEvaluationKernel_moments
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : Ω → CovariatePair d → PairVector} (hmc : Measurable (Function.uncurry c))
    (hc : ∀ᵐ w ∂designPairLaw θ,
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hE : ∀ᵐ w ∂designPairLaw θ,
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L)
    {A : PairOperator d} {B : ℝ} (hmA : Measurable (fun z : ObservationPair d × PairVector => A z.1 z.2))
    (hiA : Integrable (fun z => observationPairMask k hk z * ‖A z‖ ^ 2) (observationPairLaw θ))
    (hA : (∫ z, observationPairMask k hk z * ‖A z‖ ^ 2 ∂observationPairLaw θ) ≤ B) :
    PairKernelMoments (π.prod π) θ (pairEvaluationKernel k hk A c) (L ^ 2 * B) := by
  let := observationLaw_isProbability C θ hθ
  let q := observationPairMask (d := d) k hk
  have hmp := (observationPair_covariates_measurePreserving C θ hθ).quasiMeasurePreserving
  have hm := pilotOnObservations_measurable hmc
  have hmq : Measurable q := sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk)
  have hq (z) : q z ^ 2 = q z := by simp [q, sameLabelKernel]
  have hc' : ∀ᵐ w ∂observationPairLaw θ, q w ≠ 0 → MemLp (fun x => c x (pairCovariates w)) 2 π := hmp.ae hc
  have hE' : ∀ᵐ w ∂observationPairLaw θ, q w ≠ 0 → (∫ x, ‖c x (pairCovariates w)‖ ^ 2 ∂π) ≤ L := hmp.ae hE
  let f : Ω → ObservationPair d → PairVector := fun x z => c x (pairCovariates z)
  let K := PilotFields.maskedPilotKernel f A q
  change Measurable K ∧ MemLp K 2 _ ∧ (∫ z, K z ^ 2 ∂(π.prod π).prod (observationPairLaw θ)) ≤ _
  obtain ⟨hi, he⟩ := PilotFields.maskedPilotKernel_energy_facts
    (c := f) hm hmA hmq hq hiA hc' hE'
  exact ⟨PilotFields.maskedPilotKernel_measurable (c := f) hm hmA hmq, hi,
    he.trans (mul_le_mul_of_nonneg_left hA (sq_nonneg L))⟩

end
end NearlyMinimax
