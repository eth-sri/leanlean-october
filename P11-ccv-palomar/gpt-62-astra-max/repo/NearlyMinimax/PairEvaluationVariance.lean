module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.FieldPairVariance


@[expose] public section

/-! Full two-stage variance of the paper's actual score and denominator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

def pairEvaluationCoefficient {d : ℕ} (C : ModelConstants d) (m k : ℕ) : ℝ :=
  C.densityUpper / m + k ^ d / (2 * m * (m - 1 : ℕ))

section
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (θ : RegressionParameter d) {k : ℕ} (hk : 0 < k)
    (μ : Measure Ω) (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector)

def pairPilotVarianceBase : ℝ :=
  2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
    ∫ z, ‖η z.1 z.2‖ ^ 2
      ∂μ.prod (regularPairDesignMeasure θ k hk)

theorem pairPilotVarianceBase_nonneg :
    0 ≤ pairPilotVarianceBase θ hk μ bar η := by
  unfold pairPilotVarianceBase
  positivity

end

section
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
variable {m : ℕ} (hm : 2 ≤ m) (X : Fin m → Ξ → Observation d)
variable (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ))
include hθ hp hm hind hX

omit hp in
/-- Common evaluation-sample bound for any square-integrable same-cell field.
Both pilot kernels use the same label cap and the same two-stage inequality. -/
private theorem regularFieldAverage_sq_le
    {G : Ω × Ω → Observation d × Observation d → ℝ}
    (hmG : Measurable (Function.uncurry G))
    (hL2 : MemLp (Function.uncurry G) 2 ((μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))))
    (hsupport : ∀ p x y, regularObservationLabel hk x ≠ regularObservationLabel hk y → G p (x,y) = 0)
    {c v e : ℝ} (hv : 0 ≤ v)
    (hmean : MemLp (PairUStatistic.fieldPairMean (μ := observationLaw θ) (k^d) G) 2 (μ.prod μ) ∧
      (∫ p, (PairUStatistic.fieldPairMean (μ := observationLaw θ) (k^d) G p - c)^2 ∂μ.prod μ) ≤ v)
    (he : (∫ z, (Function.uncurry G z)^2 ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
        e / k^d) :
    (∫ z, (PairUStatistic.fieldPairAverage (k^d) G X z - c)^2 ∂(μ.prod μ).prod ν) ≤
      2 * pairEvaluationCoefficient C m k * e + 2 * v := by
  let := observationLaw_isProbability C θ hθ
  have hw : 0 < (k : ℝ)^d := by positivity
  have hU := C.one_lt_densityUpper.le
  have h := PairUStatistic.fieldPairAverage_centered_sq_le hm hind hX (regularObservationLabel_measurable hk)
    hmG hL2 hsupport hw (div_nonneg (by linarith) hw.le)
    (fun i => by rw [regularObservationLabel_mass hθ hk]; exact regularGridProbability_cap hθ hk i)
    (le_of_eq (mul_div_cancel₀ _ hw.ne')) hv hmean.1 hmean.2
  apply h.trans
  change 2 * pairEvaluationCoefficient C m k * _ + _ ≤ _
  have : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
  gcongr
  simpa only [Function.uncurry, mul_comm] using (le_div_iff₀ hw).mp he

theorem pairPilotScoreEstimate_centered_sq_le :
    let scale := (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper
    (∫ z, (PairUStatistic.fieldPairAverage (k ^ d)
      (pairPilotScoreKernel θ k hk bar η) X z -
        ∫ p, pairPilotScoreMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      2 * pairEvaluationCoefficient C m k *
        (scale) +
      (3 / 2) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
        pairPilotVarianceBase θ hk μ bar η := by
  intro scale
  have hb := pairPilotVarianceBase_nonneg θ hk μ bar η
  have hl := hp.lamNonnegative
  have hmC := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  have he := pairPilotScoreKernel_energy_le μ C θ hθ k hk bar η Cp W lam hp
  have h := regularFieldAverage_sq_le μ ν C θ hθ k hk hm X hind hX
    (G := pairPilotScoreKernel θ k hk bar η) (rawModelPairScore_measurable θ hk hmC)
    (pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp)
    (fun p x y h => by simp [pairPilotScoreKernel, pairScoreFieldKernel,
      regularObservationLabel, sameLabelKernel] at h ⊢; exact h.elim)
    (v := (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * pairPilotVarianceBase θ hk μ bar η) (by positivity)
    (pairPilotScoreMean_variance_le C θ hθ k hk μ bar η Cp lam
      (pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp))
    (e := scale) (he.trans_eq (by ring))
  apply h.trans_eq
  ring

theorem pairPilotNoiseEstimate_centered_sq_le :
    let scale := (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper
    (∫ z, (PairUStatistic.fieldPairAverage (k ^ d)
      (pairPilotNoiseKernel k hk bar η) X z -
        ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      8 * pairEvaluationCoefficient C m k *
        (scale) +
      6 * lam * pairPilotVarianceBase θ hk μ bar η := by
  intro scale
  have hb := pairPilotVarianceBase_nonneg θ hk μ bar η
  have hl := hp.lamNonnegative
  have hmC := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  have he := pairPilotNoiseKernel_energy_le μ C θ hθ k hk bar η Cp W lam hp
  have h := regularFieldAverage_sq_le μ ν C θ hθ k hk hm X hind hX
    (G := pairPilotNoiseKernel k hk bar η) (rawModelPairNoise_measurable hk hmC)
    (pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp)
    (fun p x y h => by simp [pairPilotNoiseKernel, pairNoiseFieldKernel,
      regularObservationLabel, sameLabelKernel] at h ⊢; exact h.elim)
    (v := 3 * lam * pairPilotVarianceBase θ hk μ bar η) (by positivity)
    (pairPilotNoiseMean_variance_le C θ hθ k hk μ bar η Cp lam
      (pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp))
    (e := 4 * (scale)) (he.trans_eq (by ring))
  apply h.trans_eq
  ring

end
end NearlyMinimax
