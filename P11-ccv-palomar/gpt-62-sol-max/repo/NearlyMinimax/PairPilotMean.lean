module

public import NearlyMinimax.PairOperatorMean
public import NearlyMinimax.PilotMean
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.BoundedPairMeanOperators


@[expose] public section

/-! Actual same-cell pair conditional means and their two-pilot mean risk. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

def pairPilotCoefficient {d : ℕ} (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω)
    (w : CovariatePair d) : PairVector := bar w + η x w

def pairPilotScoreKernel {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω × Ω) :
    ObservationPair d → ℝ :=
  pairScoreFieldKernel θ (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))

def pairPilotNoiseKernel {d : ℕ} (k : ℕ) (hk : 0 < k)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω × Ω) :
    ObservationPair d → ℝ :=
  pairNoiseFieldKernel (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))

def pairPilotScoreMean {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) ((k : ℝ) ^ d)
    (pairPilotScoreKernel θ k hk bar η) x

def pairPilotNoiseMean {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) ((k : ℝ) ^ d)
    (pairPilotNoiseKernel k hk bar η) x

section
variable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (x : Ω × Ω)
include hθ

private theorem pairPilotMean_eq_half {A B : CovariatePair d → PairVector →L[ℝ] PairVector}
    (hAB : B =ᵐ[regularPairDesignMeasure θ k hk] A)
    {K : (Ω × Ω) → ObservationPair d → ℝ}
    (hK : (∫ z, K x z ∂observationPairLaw θ) = ∫ w,
      sameLabelKernel (regularGridCell k hk) w *
        ⟪pairPilotCoefficient bar η x.1 w, A w (pairPilotCoefficient bar η x.2 w)⟫ ∂designPairLaw θ) :
    PairUStatistic.fieldPairMean (μ := observationLaw θ) ((k : ℝ) ^ d) K x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η B x := by
  simp only [PilotFields.pilotMean]
  rw [integral_congr_ae (hAB.mono (fun w hw => by rw [hw])),
    regularPairDesignMeasure_integral C θ hθ k hk]
  simp only [PairUStatistic.fieldPairMean, smul_eq_mul, pairPilotCoefficient, hK]
  ring

private theorem pairPilotScoreMean_eq_half_pilotMean
    (hi : Integrable (pairPilotScoreKernel θ k hk bar η x) (observationPairLaw θ)) :
    pairPilotScoreMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (boundedPairRegressionOperator C θ) x := by
  let := observationLaw_isProbability C θ hθ
  exact pairPilotMean_eq_half C θ hθ k hk bar η x
    (boundedPairRegressionOperator_eq_ae C θ hθ k hk)
    (pairScoreFieldKernel_mean C θ hθ _ _ _ hi)

private theorem pairPilotNoiseMean_eq_half_pilotMean
    (hi : Integrable (pairPilotNoiseKernel k hk bar η x) (observationPairLaw θ)) :
    pairPilotNoiseMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (fun _ => pairNoiseOperator) x := by
  let := observationLaw_isProbability C θ hθ
  exact pairPilotMean_eq_half C θ hθ k hk bar η x Filter.EventuallyEq.rfl
    (pairNoiseFieldKernel_mean C θ hθ _ _ _ hi)

end

theorem pairNoiseOperator_symmetric (a b : PairVector) :
    ⟪a, pairNoiseOperator b⟫ = ⟪pairNoiseOperator a, b⟫ := by
  simp [← real_inner_comm (pairNoiseOperator a) b, pairNoiseOperator_inner] <;> ring

theorem pairNoiseOperator_measurable_apply {W : Type*} [MeasurableSpace W] :
    Measurable (fun z : W × PairVector => pairNoiseOperator z.2) := by
  fun_prop

/-- Primitive measurable and moment conditions of the original two pilots.
No conditional mean, bias, variance, or statistical risk conclusion occurs
among these fields. -/
structure PairPilotMeanConditions {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (μ : Measure Ω) (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) (R lam : ℝ) : Prop where
  barMeasurable : Measurable bar
  barBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R
  noiseMeasurable : Measurable (fun z : Ω × (CovariatePair d) => η z.1 z.2)
  noiseMemLp : MemLp (fun z : Ω × (CovariatePair d) => η z.1 z.2) 2
    (μ.prod (regularPairDesignMeasure θ k hk))
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (CovariatePair d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk
  scoreConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotScoreKernel θ k hk bar η x)
    (observationPairLaw θ)
  noiseConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
    (observationPairLaw θ)

section ConcreteBounds
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : CovariatePair d → PairVector)
variable (η : Ω → CovariatePair d → PairVector) (R lam : ℝ)
variable (hp : PairPilotMeanConditions θ k hk μ bar η R lam)
include C hθ hp

local notation "designMeasure" => regularPairDesignMeasure θ k hk

private theorem pairPilotMean_moments {B : CovariatePair d → PairVector →L[ℝ] PairVector}
    {cB : ℝ} (hmB : Measurable (fun z : CovariatePair d × PairVector => B z.1 z.2))
    (hbound : ∀ w, ‖B w‖ ≤ cB) (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    {G : Ω × Ω → ℝ}
    (he : G =ᵐ[μ.prod μ] fun z => (1 / 2) * PilotFields.pilotMean (M := designMeasure) bar η B z) :
    MemLp G 2 (μ.prod μ) ∧
    (∫ z, G z ∂μ.prod μ) = (1 / 2) * (∫ w, ⟪bar w, B w (bar w)⟫ ∂designMeasure) ∧
    (∫ x, (G x - ∫ z, G z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      (3 / 4) * lam * cB ^ 2 * (2 * (∫ w, ‖bar w‖ ^ 2 ∂designMeasure) +
        ∫ z : Ω × CovariatePair d, ‖η z.1 z.2‖ ^ 2 ∂μ.prod designMeasure) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 designMeasure := MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  convert PilotFields.pilotMean_moments bar hp.barMeasurable hbar hp.noiseMeasurable
    hp.noiseMemLp hp.noiseCentered hmB hp.lamNonnegative hbound hsym hp.linearTest _ he using 4 <;> ring

theorem pairPilotScoreMean_moments :
    MemLp (pairPilotScoreMean θ k hk bar η) 2 (μ.prod μ) ∧
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * (∫ w, ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫ ∂designMeasure) ∧
    (∫ x, (pairPilotScoreMean θ k hk bar η x -
        ∫ z, pairPilotScoreMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * (2 * (∫ w, ‖bar w‖ ^ 2 ∂designMeasure) +
        ∫ z : Ω × CovariatePair d, ‖η z.1 z.2‖ ^ 2 ∂μ.prod designMeasure) := by
  apply pairPilotMean_moments C θ hθ k hk μ bar η R lam hp
    (boundedPairRegressionOperator_measurable_apply C θ hθ)
    (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ)
  filter_upwards [hp.scoreConditionalIntegrable] with x hx
  exact pairPilotScoreMean_eq_half_pilotMean C θ hθ k hk bar η x hx

theorem pairPilotNoiseMean_moments :
    MemLp (pairPilotNoiseMean θ k hk bar η) 2 (μ.prod μ) ∧
    (∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * (∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂designMeasure) ∧
    (∫ x, (pairPilotNoiseMean θ k hk bar η x -
        ∫ z, pairPilotNoiseMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      3 * lam * (2 * (∫ w, ‖bar w‖ ^ 2 ∂designMeasure) +
        ∫ z : Ω × CovariatePair d, ‖η z.1 z.2‖ ^ 2 ∂μ.prod designMeasure) := by
  have h := pairPilotMean_moments C θ hθ k hk μ bar η R lam hp pairNoiseOperator_measurable_apply
    (fun _ => pairNoiseOperator_norm_le) (fun _ => pairNoiseOperator_symmetric)
    (G := pairPilotNoiseMean θ k hk bar η) (B := fun _ => pairNoiseOperator) (by
      filter_upwards [hp.noiseConditionalIntegrable] with x hx
      exact pairPilotNoiseMean_eq_half_pilotMean C θ hθ k hk bar η x hx)
  refine ⟨h.1, h.2.1, ?_⟩
  convert h.2.2 using 1 <;> ring

/-- The actual conditional numerator-minus-variance-denominator mean has
bias bounded by the squared pointwise deterministic residual. -/
theorem pairPilotScoreMean_bias_le (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) ≤ (C.densityUpper / 2) * b ^ 2 := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have hOp := PilotFields.operatorField_memLp (boundedPairRegressionOperator_measurable_apply C θ hθ)
    (boundedPairRegressionOperator_norm_le C θ) hp.barMeasurable hbar
  have hInt := PilotFields.inner_integrable hbar hOp
  have hPoint : (fun w => ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫) ≤ᵐ[regularPairDesignMeasure θ k hk]
      (fun _ => b ^ 2) := by
    filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk, hresidual] with w hw hr
    rw [hw, InnerProductSpace.inner_right_rankOne_apply,
      real_inner_comm (bar w) (pairResponseVector (θ.regression w.1) (θ.regression w.2))]
    have hSq := pow_le_pow_left₀ (abs_nonneg _) hr 2
    rw [sq_abs] at hSq <;> linarith
  have hUpper := integral_mono_ae hInt (integrable_const (b ^ 2)) hPoint
  simp only [integral_const, smul_eq_mul] at hUpper
  rw [(pairPilotScoreMean_moments C θ hθ k hk μ bar η R lam hp).2.1]
  calc
    _ ≤ (1 / 2) * ((regularPairDesignMeasure θ k hk).real univ * b ^ 2) :=
      mul_le_mul_of_nonneg_left hUpper (by norm_num)
    _ ≤ (1 / 2) * (C.densityUpper * b ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2 (sq_nonneg b))
      (by norm_num)
    _ = _ := by ring

theorem pairPilotNoiseMean_denominator_lower
    (hfirst : ∀ᵐ w ∂designMeasure, bar w 0 = 1) :
    (1 / 2 : ℝ) ≤ ∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 designMeasure := MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have hOp := PilotFields.operatorField_memLp pairNoiseOperator_measurable_apply
    (fun _ => pairNoiseOperator_norm_le) hp.barMeasurable hbar
  have h := integral_mono_ae (integrable_const (1 : ℝ)) (PilotFields.inner_integrable hbar hOp) (by
    filter_upwards [hfirst] with w hw
    rw [pairNoiseOperator_inner, hw]
    nlinarith [sq_nonneg (bar w 1)])
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [(pairPilotNoiseMean_moments C θ hθ k hk μ bar η R lam hp).2.1]
  linarith [(regularPairDesignMeasure_mass_bounds C θ hθ k hk).1]

/-- The genuine conditional score mean is nonnegative because its
deterministic population operator is a positive rank-one form. -/
theorem pairPilotScoreMean_mean_nonneg :
    0 ≤ ∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ := by
  rw [(pairPilotScoreMean_moments C θ hθ k hk μ bar η R lam hp).2.1]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro w
  change 0 ≤ ⟪bar w, InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2)) (bar w)⟫
  rw [InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm (bar w)
      (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))]
  nlinarith

/-- The squared deterministic residual bounds the absolute actual score
mean, with no bias assumption on the pilot law. -/
theorem pairPilotScoreMean_abs_bias_le (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    |∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ| ≤
      (C.densityUpper / 2) * b ^ 2 := by
  rw [abs_of_nonneg (pairPilotScoreMean_mean_nonneg C θ hθ k hk μ bar η R lam hp)]
  apply pairPilotScoreMean_bias_le <;> assumption

end ConcreteBounds
end NearlyMinimax
