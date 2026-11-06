module
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.UniformPilotStatistics
public import NearlyMinimax.PaperLowerSharp
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
section
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.PairUStatistic
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
theorem fieldPairAverage_centered_sq_le {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → E) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    (label : E → I) (hlabel : Measurable label)
    {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (hsupport : ∀ p x y, label x ≠ label y → G p (x, y) = 0)
    {weight cap bound d c : ℝ} (hw : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hbound : weight * cap ≤ bound)
    (hd : 0 ≤ d)
    (hmean2 : MemLp (fieldPairMean (μ := μ) weight G) 2 π)
    (hmean : (∫ p, (fieldPairMean (μ := μ) weight G p - c) ^ 2 ∂π) ≤ d) :
    (∫ z, (fieldPairAverage n weight G X z - c) ^ 2 ∂π.prod ν) ≤
      2 * (bound / ↑n + weight / (2 * ↑n * (n - 1 : ℕ))) *
        (weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ)) + 2 * d := by
  have hmeanC : MemLp (fun p => fieldPairMean (μ := μ) weight G p - c) 2 π :=
    hmean2.sub (memLp_const c)
  have hfieldC : MemLp (fun z => fieldPairAverage n weight G X z - c) 2 (π.prod ν) :=
    (fieldPairAverage_memLp weight hG X hind hX).sub (memLp_const c)
  have hm : (∫⁻ p, ENNReal.ofReal ((fieldPairMean (μ := μ) weight G p - c) ^ 2) ∂π) ≤
      ENNReal.ofReal d := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      hmeanC.integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_mono hmean
  let a : ℝ := bound / ↑n + weight / (2 * ↑n * (n - 1 : ℕ))
  let b : P → ℝ := fun p => weight * ∫ z, G p z ^ 2 ∂μ.prod μ
  have hb : Integrable b π := hG.integrable_sq.integral_prod_left.const_mul weight
  have hb0 : ∀ᵐ p ∂π, 0 ≤ b p := Filter.Eventually.of_forall (fun p =>
    mul_nonneg hw.le (integral_nonneg (fun _ => sq_nonneg _)))
  have hbn : 0 ≤ bound := (mul_nonneg hw.le hcap).trans hbound
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : ∀ᵐ p ∂π, (∫⁻ x, ENNReal.ofReal
      ((fieldPairAverage n weight G X (p, x) - fieldPairMean (μ := μ) weight G p) ^ 2) ∂ν) ≤
      ENNReal.ofReal (a * b p) := by
    filter_upwards [PilotFields.memLp_sections hG] with p hp
    have hmGp : Measurable (G p) := hmG.comp (measurable_const.prodMk measurable_id)
    have hT : MemLp (fun x => fieldPairAverage n weight G X (p, x) -
        fieldPairMean (μ := μ) weight G p) 2 ν :=
      (pairAverage_memLp_two X hind hX (weightedSymmetrization_memLp weight hp)).sub (memLp_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal hT.integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_mono (weighted_pair_centered_sq_le hn X hind hX label hlabel
      hmGp hp (hsupport p) hw hcap hmass hbound)
  have h_fieldPairMean_measurable : Measurable (fieldPairMean (μ := μ) weight G) := hmG.stronglyMeasurable.integral_prod_right'.measurable.const_mul _
  have hr := NearlyMinimax.two_stage_mean_squared_bound π ν
    (fieldPairAverage n weight G X) (fieldPairMean (μ := μ) weight G) b
    (fieldPairAverage_measurable n weight hmG X (fun i => (hX i).measurable))
    h_fieldPairMean_measurable hb hb0 ha hd hc hm
  have he : (∫ p, b p ∂π) = weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ) := by
    rw [integral_const_mul, integral_prod _ hG.integrable_sq]
  have hr := by simpa only [he, a] using hr
  rw [← ofReal_integral_eq_lintegral_ofReal
    hfieldC.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at hr
  have : 0 ≤ bound := (mul_nonneg hw.le hcap).trans hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by
    positivity)).1 hr
end NearlyMinimax.PairUStatistic
namespace NearlyMinimax
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace BigOperators
def pairEvaluationCoefficient  (C : ModelConstants d) (m k : ℕ) : ℝ :=
  C.densityUpper / m + k ^ d / (2 * m * (m - 1 : ℕ))
def pairPilotVarianceBase  [MeasurableSpace Ω] 
    (θ : RegressionParameter d) (k ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) : ℝ :=
  2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
    ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
      ∂μ.prod (regularPairDesignMeasure θ k hk)
theorem pairPilotVarianceBase_nonneg  [MeasurableSpace Ω] 
    (θ k hk μ bar)
    (η : Ω → Covariate d × Covariate d → PairVector) :
    0 ≤ pairPilotVarianceBase θ k hk μ bar η := by
  unfold pairPilotVarianceBase
  positivity
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
end
section
namespace PairUStatistic
variable {d n m : ℕ} {Cp a : ℝ}
variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E]
theorem fieldPairAverage_add_smul (n : ℕ) (weight V : ℝ)
    (G H : P → E × E → ℝ) (X : Fin n → Ω → E) (z : P × Ω) :
    fieldPairAverage n weight (fun p w => G p w + V * H p w) X z =
      fieldPairAverage n weight G X z + V * fieldPairAverage n weight H X z := by
  unfold fieldPairAverage pairAverage weightedSymmetrization
  simp only [Prod.swap_prod_mk]
  have hpoint : ∀ i j : Fin n,
      weight / 4 * (G z.1 (X i z.2, X j z.2) + V * H z.1 (X i z.2, X j z.2) +
        (G z.1 (X j z.2, X i z.2) + V * H z.1 (X j z.2, X i z.2))) =
      weight / 4 * (G z.1 (X i z.2, X j z.2) + G z.1 (X j z.2, X i z.2)) +
      V * (weight / 4 * (H z.1 (X i z.2, X j z.2) + H z.1 (X j z.2, X i z.2))) := by
    intros; ring
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end PairUStatistic
def pairPilotNumeratorKernel   (k ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω)
    (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪pairPilotCoefficient bar η p.1 (pairCovariates z),
      InnerProductSpace.rankOne ℝ (pairResponseVector z.1.2 z.2.2)
        (pairResponseVector z.1.2 z.2.2)
          (pairPilotCoefficient bar η p.2 (pairCovariates z))⟫
end
def pairRiskBudget  (C : ModelConstants d) (m k : ℕ)
    (Cp W lam B b a : ℝ) : ℝ :=
  (2 / a ^ 2) *
    (4 * pairEvaluationCoefficient C m k *
      (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper +
    3 * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * B +
    2 * ((C.densityUpper / 2) * b ^ 2) ^ 2 +
    C.varianceUpper ^ 2 *
      (8 * pairEvaluationCoefficient C m k *
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper + 6 * lam * B))
theorem integral_sq_le_twice_centered {Z : Type*} [MeasurableSpace Z]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] {S : Z → ℝ} (hS : MemLp S 2 ρ) (c : ℝ) :
    (∫ z, S z ^ 2 ∂ρ) ≤ 2 * (∫ z, (S z - c) ^ 2 ∂ρ) + 2 * c ^ 2 := by
  have hc : MemLp (fun z => S z - c) 2 ρ := hS.sub (memLp_const c)
  have h : (∫ z, S z ^ 2 ∂ρ) ≤ ∫ z, 2 * (S z - c) ^ 2 + 2 * c ^ 2 ∂ρ :=
    integral_mono hS.integrable_sq ((hc.integrable_sq.const_mul 2).add (integrable_const (2 * c ^ 2))) (fun z => by nlinarith [sq_nonneg (S z - 2 * c)])
  rw [integral_add (hc.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul] at h
  simpa using h
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
theorem common_pair_ratio_risk_le (b a ) (ha : 0 < a)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b)
    (hfloor : 2 * a ≤ ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper a
        (PairUStatistic.fieldPairAverage m (k ^ d) (pairPilotNumeratorKernel k hk bar η) X)
        (PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotNoiseKernel k hk bar η) X) z -
          θ.variance) ^ 2) ∂(μ.prod μ).prod ν) ≤
    ENNReal.ofReal (pairRiskBudget C m k Cp W lam
      (pairPilotVarianceBase θ k hk μ bar η) b a) := by
  let := observationLaw_isProbability C θ hθ
  let S := PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotScoreKernel θ k hk bar η) X
  let D := PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotNoiseKernel k hk bar η) X
  let N := PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotNumeratorKernel k hk bar η) X
  have hmc := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  have hmS : Measurable S := PairUStatistic.fieldPairAverage_measurable _ _
    (rawModelPairScore_measurable θ k hk hmc) X (fun i => (hX i).measurable)
  have hmD : Measurable D := PairUStatistic.fieldPairAverage_measurable _ _
    (rawModelPairNoise_measurable k hk hmc) X (fun i => (hX i).measurable)
  have hS : MemLp S 2 ((μ.prod μ).prod ν) := PairUStatistic.fieldPairAverage_memLp _
    (pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  have hD : MemLp D 2 ((μ.prod μ).prod ν) := PairUStatistic.fieldPairAverage_memLp _
    (pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  have he : N = fun z => S z + θ.variance * D z := by
    funext z
    dsimp [N, S, D]
    have h_pairPilotNumeratorKernel_eq_score_add_noise (k : ℕ) (hk : 0 < k) (bar : Covariate d × Covariate d → PairVector) (η : Ω → Covariate d × Covariate d → PairVector) : pairPilotNumeratorKernel k hk bar η =
      (fun p z => pairPilotScoreKernel θ k hk bar η p z +
        θ.variance * pairPilotNoiseKernel k hk bar η p z) := by
      funext p z
      have hq : sameLabelKernel (regularObservationLabel k hk) z =
          sameLabelKernel (regularGridCell k hk) (z.1.1, z.2.1) := rfl
      simp only [pairPilotNumeratorKernel, pairPilotScoreKernel, pairPilotNoiseKernel,
        pairScoreFieldKernel, pairNoiseFieldKernel, pairCovariates, regularObservationLabel,
        pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_right, inner_smul_right]
      rw [hq]
      ring
    rw [h_pairPilotNumeratorKernel_eq_score_add_noise]
    exact PairUStatistic.fieldPairAverage_add_smul _ _ _ _ _ _ _
  have hmN : Measurable N := by rw [he]; exact hmS.add (hmD.const_mul _)
  have hdif : (fun z => N z - θ.variance * D z) = S := by
    rw [he]
    funext z
    ring
  have hgap : MemLp (fun z => N z - θ.variance * D z) 2 ((μ.prod μ).prod ν) := by rw [hdif]; exact hS
  have hvlo := hθ.2.2.2.2.2.1
  have hvhi := hθ.2.2.2.2.2.2.1
  have hr := stabilized_ratio_lintegral_mse_le ((μ.prod μ).prod ν) hmN hmD hgap hD
    ha hvlo hvhi (C.varianceLower_pos.le.trans hvlo) hfloor
  simp_rw [fun z => congrFun hdif z] at hr
  have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
  have h_pairPilotScoreMean_abs_bias_le : |∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ| ≤
      (C.densityUpper / 2) * b ^ 2 := by
    rw [abs_of_nonneg (pairPilotScoreMean_mean_nonneg C θ hθ k hk μ bar η Cp lam hM)]
    exact pairPilotScoreMean_bias_le C θ hθ k hk μ bar η Cp lam hM b hresidual
  have hb := h_pairPilotScoreMean_abs_bias_le
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hb2
  have h_pairPilotScoreEstimate_centered_sq_le : (∫ z, (PairUStatistic.fieldPairAverage m (↑k ^ d)
      (pairPilotScoreKernel θ k hk bar η) X z -
        ∫ p, pairPilotScoreMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      2 * pairEvaluationCoefficient C m k *
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper +
      (3 / 2) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
        pairPilotVarianceBase θ k hk μ bar η := by
    let := observationLaw_isProbability C θ hθ
    have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
    have h_pairPilotScoreMean_variance_le : MemLp (pairPilotScoreMean θ k hk bar η) 2 (μ.prod μ) ∧
        (∫ x, (pairPilotScoreMean θ k hk bar η x -
          ∫ z, pairPilotScoreMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
        (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
          (2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
            ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
              ∂μ.prod (regularPairDesignMeasure θ k hk)) := by
      let := regularPairDesignMeasure_isFinite C θ hθ k hk
      exact half_pilotMean_variance_transfer bar hM.barMeasurable (MemLp.of_bound hM.barMeasurable.aestronglyMeasurable Cp hM.barBound) hM.noiseMeasurable hM.noiseMemLp hM.noiseCentered
        (boundedPairRegressionOperator_measurable_apply C θ hθ) (by positivity) hM.lamNonnegative
        (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ)
        hM.linearTest _ (by filter_upwards [hM.scoreConditionalIntegrable] with x hx; exact pairPilotScoreMean_eq_half_pilotMean C θ hθ k hk bar η x hx)
    obtain ⟨hmean, hvar⟩ := h_pairPilotScoreMean_variance_le
    have hmeas := rawModelPairScore_measurable θ k hk
      (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    have hL2 := pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp
    have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
    have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
    have hd0 : 0 ≤ (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
        pairPilotVarianceBase θ k hk μ bar η := by
      have hb := pairPilotVarianceBase_nonneg θ k hk μ bar η
      have hl := hp.lamNonnegative
      positivity
    have hr := PairUStatistic.fieldPairAverage_centered_sq_le
      (π := μ.prod μ) (ν := ν) (μ := observationLaw θ)
      (G := pairPilotScoreKernel θ k hk bar η)
      (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm X hind hX
      (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
      hmeas hL2
      (fun p x y hxy => by simp [rawModelPairScore, pairPilotScoreKernel, pairScoreFieldKernel,
        regularObservationLabel, pairCovariates, sameLabelKernel] at hxy ⊢; exact hxy.elim)
      hkp (div_nonneg hpplus hkp.le)
      (fun i => by
        rw [regularObservationLabel_mass C θ hθ k hk i]
        exact regularGridProbability_cap C θ hθ k hk i)
      (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
    have h_pairPilotScoreKernel_energy_le : (∫ z : (Ω × Ω) × (Observation d × Observation d),
        pairPilotScoreKernel θ k hk bar η z.1 z.2 ^ 2
        ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 *
          (responseOperatorEnergyBound C * (C.densityUpper / ↑k ^ d)) := by
      exact rawModelPairScore_energy_le μ C θ hθ k hk
        (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
        (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
        (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
          mul_nonneg hp.constantNonnegative hp.budgetNonnegative])
        (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)
    have he := h_pairPilotScoreKernel_energy_le
    have hE : ↑k ^ d *
        (∫ z : (Ω × Ω) × (Observation d × Observation d),
          pairPilotScoreKernel θ k hk bar η z.1 z.2 ^ 2
            ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper := by
      apply (mul_le_mul_of_nonneg_left he hkp.le).trans_eq
      field_simp
    have heval : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
    apply hr.trans
    change 2 * pairEvaluationCoefficient C m k * _ + 2 *
      ((3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * pairPilotVarianceBase θ k hk μ bar η) ≤ _
    have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * pairEvaluationCoefficient C m k)
    nlinarith
  have := h_pairPilotScoreEstimate_centered_sq_le
  have h_pairPilotNoiseEstimate_centered_sq_le : (∫ z, (PairUStatistic.fieldPairAverage m (↑k ^ d)
      (pairPilotNoiseKernel k hk bar η) X z -
        ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      8 * pairEvaluationCoefficient C m k *
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper +
      6 * lam * pairPilotVarianceBase θ k hk μ bar η := by
    let := observationLaw_isProbability C θ hθ
    have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
    have h_pairPilotNoiseMean_variance_le : MemLp (pairPilotNoiseMean θ k hk bar η) 2 (μ.prod μ) ∧
        (∫ x, (pairPilotNoiseMean θ k hk bar η x -
          ∫ z, pairPilotNoiseMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
        3 * lam * (2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
          ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
            ∂μ.prod (regularPairDesignMeasure θ k hk)) := by
      let := regularPairDesignMeasure_isFinite C θ hθ k hk
      obtain ⟨hL2, hVar⟩ := half_pilotMean_variance_transfer bar hM.barMeasurable (MemLp.of_bound hM.barMeasurable.aestronglyMeasurable Cp hM.barBound)
        hM.noiseMeasurable hM.noiseMemLp hM.noiseCentered pairNoiseOperator_measurable_apply
        (by norm_num : (0 : ℝ) ≤ 2) hM.lamNonnegative (fun _ => pairNoiseOperator_norm_le)
        (fun _ => pairNoiseOperator_symmetric) hM.linearTest _ (by filter_upwards [hM.noiseConditionalIntegrable] with x hx; exact pairPilotNoiseMean_eq_half_pilotMean C θ hθ k hk bar η x hx)
      refine ⟨hL2, ?_⟩
      convert hVar using 1 <;> ring
    obtain ⟨hmean, hvar⟩ := h_pairPilotNoiseMean_variance_le
    have hmeas := rawModelPairNoise_measurable k hk
      (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    have hL2 := pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp
    have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
    have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
    have hd0 : 0 ≤ 3 * lam * pairPilotVarianceBase θ k hk μ bar η := by
      have hb := pairPilotVarianceBase_nonneg θ k hk μ bar η
      have hl := hp.lamNonnegative
      positivity
    have hr := PairUStatistic.fieldPairAverage_centered_sq_le
      (π := μ.prod μ) (ν := ν) (μ := observationLaw θ)
      (G := pairPilotNoiseKernel k hk bar η)
      (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm X hind hX
      (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
      hmeas hL2
      (fun p x y hxy => by simp [rawModelPairNoise, pairPilotNoiseKernel, pairNoiseFieldKernel,
        regularObservationLabel, pairCovariates, sameLabelKernel] at hxy ⊢; exact hxy.elim)
      hkp (div_nonneg hpplus hkp.le)
      (fun i => by
        rw [regularObservationLabel_mass C θ hθ k hk i]
        exact regularGridProbability_cap C θ hθ k hk i)
      (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
    have h_pairPilotNoiseKernel_energy_le : (∫ z : (Ω × Ω) × (Observation d × Observation d),
        pairPilotNoiseKernel k hk bar η z.1 z.2 ^ 2
        ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
        (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * (4 * (C.densityUpper / ↑k ^ d)) := by
      exact rawModelPairNoise_energy_le μ C θ hθ k hk
        (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
        (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
        (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
          mul_nonneg hp.constantNonnegative hp.budgetNonnegative])
        (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)
    have he := h_pairPilotNoiseKernel_energy_le
    have hE : ↑k ^ d *
        (∫ z : (Ω × Ω) × (Observation d × Observation d),
          pairPilotNoiseKernel k hk bar η z.1 z.2 ^ 2
            ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
        4 * (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper := by
      apply (mul_le_mul_of_nonneg_left he hkp.le).trans_eq
      field_simp
    have : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
    apply hr.trans
    change 2 * pairEvaluationCoefficient C m k * _ + 2 *
      (3 * lam * pairPilotVarianceBase θ k hk μ bar η) ≤ _
    have := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * pairEvaluationCoefficient C m k)
    nlinarith
  have hDv := h_pairPilotNoiseEstimate_centered_sq_le
  have := integral_sq_le_twice_centered ((μ.prod μ).prod ν) hS
    (∫ p, pairPilotScoreMean θ k hk bar η p ∂μ.prod μ)
  apply hr.trans
  apply ENNReal.ofReal_mono
  unfold pairRiskBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 / a ^ 2)
  apply add_le_add
  · change (∫ z, S z ^ 2 ∂(μ.prod μ).prod ν) ≤ _
    nlinarith
  · exact mul_le_mul_of_nonneg_left hDv (sq_nonneg _)
end
def pairFluctuationScale {d : ℕ} (n k : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ + Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)
theorem pairFluctuationScale_nonneg {d : ℕ} (n k : ℕ) :
    0 ≤ pairFluctuationScale (d := d) n k := by unfold pairFluctuationScale; positivity
theorem pairFluctuationScale_sq_lower {d : ℕ} (n k : ℕ) (hn : 0 < n) :
    1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2 ≤ pairFluctuationScale (d := d) n k ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = 1 / (n : ℝ) := by
    rw [inv_pow, Real.sq_sqrt hn0.le]; simp [one_div]
  have : (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) ^ 2 = (k : ℝ) ^ d / (n : ℝ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) := by positivity
  unfold pairFluctuationScale
  nlinarith
def pairRateSquaredConstant  (C : ModelConstants d) (Cp c a : ℝ) : ℝ :=
  (2 / a ^ 2) *
    ((4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
      4 * (C.densityUpper / c + 1 / c ^ 2) * (1 + Cp) ^ 4 +
    (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
      2 * C.densityUpper * (1 + Cp) ^ 4 + C.densityUpper ^ 2 / 2)
theorem pairRateSquaredConstant_pos  (C : ModelConstants d)
    {Cp c a : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c) (ha : 0 < a) :
    0 < pairRateSquaredConstant C Cp c a := by
  have : 0 < C.densityUpper := by linarith [C.one_lt_densityUpper]
  have := responseOperatorEnergyBound_pos C
  unfold pairRateSquaredConstant
  positivity
section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hθ hp
theorem pairPilotVarianceBase_le :
    pairPilotVarianceBase θ k hk μ bar η ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hb := regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound
  have : (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) ≤
      Cp ^ 2 * (regularPairDesignMeasure θ k hk).real univ := by
    have h := integral_mono_ae (MemLp.of_bound hp.barMeasurable.aestronglyMeasurable Cp hb).norm.integrable_sq (integrable_const (Cp ^ 2))
      (hb.mono (fun w hw => pow_le_pow_left₀ (norm_nonneg _) hw 2))
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  have := PilotFields.joint_energy_le_of_uniform_sections hp.noiseMeasurable (regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection)
    (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) (regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy)
  have hmass := (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2
  have := mul_le_mul_of_nonneg_left hmass (sq_nonneg Cp)
  have := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hp.constantNonnegative hp.budgetNonnegative)
  unfold pairPilotVarianceBase
  nlinarith
end
theorem paper_common_pair_rms {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
     (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W : ℝ)
    {n m : ℕ} (hn : 0 < n) (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c)
    (hsize : c * (n : ℝ) ≤ m)
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (X : Fin m → Ξ → Observation d) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ)) (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
        (PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotNumeratorKernel k hk bar η) X)
        (PairUStatistic.fieldPairAverage m (↑k ^ d) (pairPilotNoiseKernel k hk bar η) X) z -
          θ.variance) ^ 2) ∂(μ.prod μ).prod ν) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp c (1 / 4)) *
      (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  have h_pairPilotNoiseMean_denominator_lower (lam : ℝ) (hp : PairPilotMeanConditions θ k hk μ bar η Cp lam) : (1 / 2 ) ≤ ∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ := pairPilotNoiseMean_mean_lower C θ hθ k hk μ bar η hp.barMeasurable Cp hp.barBound hfirst
    hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered lam hp.lamNonnegative hp.linearTest hp.noiseConditionalIntegrable
  have hr := common_pair_ratio_risk_le μ ν C θ hθ k hk bar η Cp W _ hp hm X hind hX
    b (1 / 4) (by norm_num) hresidual (by have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W _ hp; norm_num only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num]; exact (h_pairPilotNoiseMean_denominator_lower _ hM))
  have h_pairRiskBudget_rate_le {d : ℕ} {lam : ℝ} {B : ℝ} {a : ℝ} {Cp : ℝ} {W : ℝ} (C : ModelConstants d) (hCp : 0 ≤ Cp) (hW : 0 ≤ W) (hlam : 0 ≤ lam) (hB : 0 ≤ B) (ha : 0 < a) (hlamBudget : lam ≤ Cp ^ 2 * W / n) (hBBudget : B ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W)) : pairRiskBudget C m k Cp W lam B b a ≤ pairRateSquaredConstant C Cp c a *
      (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W)) ^ 2 := by
    let P := 1 + Cp
    let t := pairFluctuationScale (d := d) n k
    let R := t * (1 + W)
    let E := C.densityUpper / c + 1 / c ^ 2
    let F := 2 * Cp ^ 2 + 2 * Cp * W
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
    have := (responseOperatorEnergyBound_pos C).le
    have : 0 ≤ P := by dsimp [P]; positivity
    have ht : 0 ≤ t := pairFluctuationScale_nonneg n k
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have : 0 ≤ E := by dsimp [E]; positivity
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hCP : Cp ≤ P ^ 2 := by dsimp [P]; nlinarith only [hCp, sq_nonneg Cp]
    have hC2P : Cp ^ 2 ≤ P ^ 2 := by dsimp [P]; nlinarith only [hCp]
    have hCW := mul_le_mul_of_nonneg_right hCP hW
    have hFb : F ≤ 2 * P ^ 2 * (1 + W) := by dsimp [F]; nlinarith only [hC2P, hCW]
    have hF2 : F ^ 2 ≤ 4 * P ^ 4 * (1 + W) ^ 2 := by
      apply (pow_le_pow_left₀ hF hFb 2).trans_eq
      ring
    have h_pairEvaluationCoefficient_rate_le : pairEvaluationCoefficient C m k ≤
        (C.densityUpper / c + 1 / c ^ 2) * pairFluctuationScale (d := d) n k ^ 2 := by
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
      have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hpp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
      have hk0 : 0 ≤ (k : ℝ) ^ d := by positivity
      have hm1 : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
      have  :=
        pow_le_pow_left₀ (by positivity) hsize 2
      have hden : c ^ 2 * (n : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (m - 1 : ℕ) := by
        have h := mul_le_mul_of_nonneg_left hm1 hm0.le
        nlinarith
      have hfirst  :=
        div_le_div_of_nonneg_left hpp (by positivity) hsize
      have hsecond  :=
        div_le_div_of_nonneg_left hk0 (by positivity) hden
      have hA : 0 ≤ C.densityUpper / c + 1 / c ^ 2 := by positivity
      have h1 : C.densityUpper / c ≤ C.densityUpper / c + 1 / c ^ 2 := le_add_of_nonneg_right (by positivity)
      have h2 : 1 / c ^ 2 ≤ C.densityUpper / c + 1 / c ^ 2 := le_add_of_nonneg_left (by positivity)
      calc
        _ ≤ C.densityUpper / (c * n) + (k : ℝ) ^ d / (c ^ 2 * (n : ℝ) ^ 2) :=
          add_le_add hfirst hsecond
        _ = (C.densityUpper / c) * (1 / (n : ℝ)) +
            (1 / c ^ 2) * ((k : ℝ) ^ d / (n : ℝ) ^ 2) := by ring
        _ ≤ (C.densityUpper / c + 1 / c ^ 2) *
            (1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2) := by
          have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 1 / (n : ℝ))
          have := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ (k : ℝ) ^ d / (n : ℝ) ^ 2)
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (pairFluctuationScale_sq_lower n k hn) hA
    have he := h_pairEvaluationCoefficient_rate_le
    have : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
    have hEF : pairEvaluationCoefficient C m k * F ^ 2 ≤ 4 * E * P ^ 4 * R ^ 2 := by
      have h := mul_le_mul he hF2 (sq_nonneg F) (by positivity)
      apply h.trans_eq
      ring
    have hBb : B ≤ 2 * C.densityUpper * P ^ 2 * (1 + W) := by
      have h := mul_le_mul_of_nonneg_left (show 2 * Cp ^ 2 + Cp * W ≤ 2 * P ^ 2 * (1 + W) by nlinarith only [hC2P, hCW, mul_nonneg (sq_nonneg P) hW]) hpp
      apply (hBBudget.trans h).trans_eq
      ring
    have hLamSmall := hlamBudget.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2P hW) hn0.le)
    have hLamB : lam * B ≤ 2 * C.densityUpper * P ^ 4 * R ^ 2 := by
      have hmB := mul_le_mul hLamSmall hBb hB (by positivity : 0 ≤ P ^ 2 * W / (n : ℝ))
      have : W * (1 + W) ≤ (1 + W) ^ 2 := by nlinarith only [hW]
      have : 1 / (n : ℝ) ≤ t ^ 2 := by
        have := pairFluctuationScale_sq_lower (d := d) n k hn
        have : 0 ≤ (k : ℝ) ^ d / (n : ℝ) ^ 2 := by positivity
        linarith
      calc
        _ ≤ (P ^ 2 * W / (n : ℝ)) * (2 * C.densityUpper * P ^ 2 * (1 + W)) := hmB
        _ = (2 * C.densityUpper * P ^ 4) * (W * (1 + W)) * (1 / (n : ℝ)) := by ring
        _ ≤ (2 * C.densityUpper * P ^ 4) * (1 + W) ^ 2 * (1 / (n : ℝ)) := by gcongr
        _ ≤ (2 * C.densityUpper * P ^ 4) * (1 + W) ^ 2 * t ^ 2 := by gcongr
        _ = _ := by dsimp [R]; ring
    have hA0 : 0 ≤ 4 * responseOperatorEnergyBound C * C.densityUpper +
        8 * C.varianceUpper ^ 2 * C.densityUpper := by positivity
    have hL0 : 0 ≤ 3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2 := by positivity
    have hER := mul_le_mul_of_nonneg_left hEF hA0
    have hLR := mul_le_mul_of_nonneg_left hLamB hL0
    have hsR  :=
      pow_le_pow_left₀ hR (le_add_of_nonneg_left (sq_nonneg b)) 2
    have hh := pow_le_pow_left₀ (sq_nonneg b) (le_add_of_nonneg_right hR) 2
    have hCR : 0 ≤ (4 * responseOperatorEnergyBound C * C.densityUpper +
        8 * C.varianceUpper ^ 2 * C.densityUpper) * 4 * E * P ^ 4 +
        (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
          (2 * C.densityUpper * P ^ 4) := by positivity
    have hCsb := mul_le_mul_of_nonneg_left (by simpa only [← pow_mul] using hh) (by positivity : 0 ≤ C.densityUpper ^ 2 / 2)
    have hCsR := mul_le_mul_of_nonneg_left hsR hCR
    have hbudget : pairRiskBudget C m k Cp W lam B b a =
        (2 / a ^ 2) *
          ((4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
            pairEvaluationCoefficient C m k * F ^ 2 +
          (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) * lam * B +
          (C.densityUpper ^ 2 / 2) * b ^ 4) := by unfold pairRiskBudget F; ring
    rw [hbudget]
    unfold pairRateSquaredConstant
    change (2 / a ^ 2) * _ ≤ (2 / a ^ 2) * _ * (b ^ 2 + R) ^ 2
    rw [mul_assoc (2 / a ^ 2) _ ((b ^ 2 + R) ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 / a ^ 2)
    linarith only [hER, hLR, hCsR, hCsb]
  have hC0 := (pairRateSquaredConstant_pos C hp.constantNonnegative hc (by norm_num : (0 : ℝ) < 1 / 4)).le
  have hrms := ENNReal.rpow_le_rpow (hr.trans (ENNReal.ofReal_mono (h_pairRiskBudget_rate_le C hp.constantNonnegative hp.budgetNonnegative hp.lamNonnegative (pairPilotVarianceBase_nonneg θ k hk μ bar η) (by norm_num : (0 : ℝ) < 1 / 4) le_rfl (pairPilotVarianceBase_le μ C θ hθ k hk bar η Cp W _ hp)))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC0 (sq_nonneg _)) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hC0, Real.sqrt_sq (by have := pairFluctuationScale_nonneg (d := d) n k; have := hp.budgetNonnegative; positivity)] at hrms
  exact hrms
def coefficientPairNumeratorKernel   (k ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω)
    (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), InnerProductSpace.rankOne ℝ
      (pairResponseVector z.1.2 z.2.2) (pairResponseVector z.1.2 z.2.2)
        (c p.2 (pairCovariates z))⟫
theorem coefficientPairNumeratorKernel_measurable  [MeasurableSpace Ω] 
    (k hk) 
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      coefficientPairNumeratorKernel k hk c z.1 z.2) := by
  have hm := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun z => pairScoreOperator 0 z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) 0)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  change Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) =>
    sameLabelKernel (regularObservationLabel k hk) z.2 *
      ⟪c z.1.1 (pairCovariates z.2), pairScoreOperator 0 z.2.1.2 z.2.2.2
        (c z.1.2 (pairCovariates z.2))⟫) at hm
  simpa only [coefficientPairNumeratorKernel, pairScoreOperator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, zero_smul, sub_zero] using hm
def coefficientPairStatistic  (C : ModelConstants d) (m k ) (hk : 0 < k)
    (c : (Fin m → Observation d) → Covariate d × Covariate d → PairVector)
    (z : (((Fin m → Observation d) × (Fin m → Observation d)) × (Fin m → Observation d))) : ℝ :=
  stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
    (PairUStatistic.fieldPairAverage m (k ^ d) (coefficientPairNumeratorKernel k hk c)
      (fun i x => x i))
    (PairUStatistic.fieldPairAverage m (k ^ d) (rawModelPairNoise k hk c)
      (fun i x => x i)) z
def coefficientPairEstimator  (C : ModelConstants d) (k ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (Covariate d × Covariate d) => c z.1 z.2)) : Estimator d n :=
  threeBlockEstimator (coefficientPairStatistic C (threeBlockSize n) k hk c)
    (stabilizedRatio_measurable C.varianceLower C.varianceUpper (1 / 4)
      (PairUStatistic.fieldPairAverage_measurable _ (k ^ d)
        (coefficientPairNumeratorKernel_measurable k hk hmc)
        (fun (i : Fin _) (x : Fin _ → Observation d) => x i) (fun i => measurable_pi_apply i))
      (PairUStatistic.fieldPairAverage_measurable _ (k ^ d)
        (rawModelPairNoise_measurable k hk hmc)
        (fun (i : Fin _) (x : Fin _ → Observation d) => x i) (fun i => measurable_pi_apply i)))
theorem coefficientPairEstimator_rms_bound  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 6 ≤ n)
    (k hk c hmc bar η Cp W b) (heq : c = pairPilotCoefficient bar η)
    (hp : PairPilotAssumptions θ k hk (sampleLaw θ (threeBlockSize n)) bar η
      Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
        (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ (threeBlockSize n)
  have hi := iIndepFun_pi (μ := fun _ : Fin (threeBlockSize n) => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := paper_common_pair_rms (sampleLaw θ (threeBlockSize n)) (sampleLaw θ (threeBlockSize n))
    C θ hθ k hk bar η Cp W (by omega : 0 < n) (threeBlockSize_two_le hn)
    (by norm_num : (0 : ℝ) < 1 / 4) (threeBlockSize_fraction hn) hp hfirst
    (fun i x => x i) hi (fun i => measurePreserving_eval (fun _ : Fin (threeBlockSize n) => observationLaw θ) i) b hresidual
  unfold coefficientPairEstimator
  have h_threeBlockEstimator_risk_eq (T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ) (hmT : Measurable T) : meanSquaredRisk (threeBlockEstimator T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ (threeBlockSize n)).prod (sampleLaw θ (threeBlockSize n))).prod
          (sampleLaw θ (threeBlockSize n)) := by
    rw [threeBlockEstimator, castEstimator_risk_eq]
    exact blockEstimatorWithRemainder_risk_eq C θ hθ T hmT
  rw [h_threeBlockEstimator_risk_eq]
  have hnum : coefficientPairNumeratorKernel k hk (pairPilotCoefficient bar η) =
      pairPilotNumeratorKernel k hk bar η := rfl
  have hden : rawModelPairNoise k hk (pairPilotCoefficient bar η) =
      pairPilotNoiseKernel k hk bar η := rfl
  simp_rw [coefficientPairStatistic, heq, hnum, hden]
  exact h
theorem minimaxRMS_le_of_estimator_rms  (C : ModelConstants d)
    (T : Estimator d n) {B : ℝ≥0∞}
    (hT : ∀ θ : RegressionParameter d, Admissible C θ → meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ B) :
    minimaxRMS C n ≤ B := by
  have h := ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk C T)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply h.trans
  let φ := ENNReal.orderIsoRpow (1 / 2 ) (by norm_num)
  change φ (⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val) ≤ B
  rw [φ.map_iSup]
  exact iSup_le (fun θ => hT θ.val θ.property)
end NearlyMinimax
end
open MeasureTheory Filter Matrix
open scoped RealInnerProductSpace Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
def twoScalarPilotVector (a b : ℝ) : PairVector :=
  (a - b) • pairCoordinateVector 1 - a • pairCoordinateVector 2
theorem twoScalarPilotVector_coordinates (a b ) :
    twoScalarPilotVector a b = WithLp.toLp 2 ![0, a - b, -a] := by
  ext i
  fin_cases i <;> simp [twoScalarPilotVector, pairCoordinateVector]
theorem twoScalarPilotVector_norm_sq_le (a b ) :
    ‖twoScalarPilotVector a b‖ ^ 2 ≤ 3 * a ^ 2 + 2 * b ^ 2 := by
  have h_twoScalarPilotVector_norm_sq : ‖twoScalarPilotVector a b‖ ^ 2 = (a - b) ^ 2 + a ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, twoScalarPilotVector_coordinates]
    simp [Fin.sum_univ_succ]
  rw [h_twoScalarPilotVector_norm_sq]
  nlinarith only [sq_nonneg (a + b)]
theorem twoScalarPilotVector_inner (a b v) :
    ⟪twoScalarPilotVector a b, v⟫ = (v 1 - v 2) * a - v 1 * b := by
  rw [twoScalarPilotVector_coordinates]
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ]
  ring
section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {a b : Ω → ℝ}
theorem twoScalarPilotVector_memLp (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun x => twoScalarPilotVector (a x) (b x)) 2 μ := by
  have h_twoScalarPilotVector_aestronglyMeasurable : AEStronglyMeasurable (fun x => twoScalarPilotVector (a x) (b x)) μ := ((ha.aestronglyMeasurable.sub hb.aestronglyMeasurable).smul_const _).sub (ha.aestronglyMeasurable.smul_const _)
  have hs := h_twoScalarPilotVector_aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hs).2
  apply ((ha.integrable_sq.const_mul 3).add (hb.integrable_sq.const_mul 2)).mono' (hs.norm.pow 2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact twoScalarPilotVector_norm_sq_le _ _
theorem twoScalarPilotVector_mean_zero [IsFiniteMeasure μ]
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hma : (∫ x, a x ∂μ) = 0) (hmb : (∫ x, b x ∂μ) = 0) :
    (∫ x, twoScalarPilotVector (a x) (b x) ∂μ) = 0 := by
  have hai  := ha.integrable (by norm_num)
  have hbi  := hb.integrable (by norm_num)
  have hs1 : Integrable (fun x => (a x - b x) • pairCoordinateVector 1) μ := (hai.sub hbi).smul_const _
  have hs2 : Integrable (fun x => a x • pairCoordinateVector 2) μ := hai.smul_const _
  unfold twoScalarPilotVector
  rw [integral_sub hs1 hs2,
    integral_smul_const, integral_smul_const, integral_sub hai hbi, hma, hmb]
  simp
theorem twoScalarPilotVector_second_le (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
     (hEa : (∫ x, a x ^ 2 ∂μ) ≤ E) (hEb : (∫ x, b x ^ 2 ∂μ) ≤ E) :
    (∫ x, ‖twoScalarPilotVector (a x) (b x)‖ ^ 2 ∂μ) ≤ 5 * E := by
  have h := integral_mono (twoScalarPilotVector_memLp ha hb).norm.integrable_sq
    ((ha.integrable_sq.const_mul 3).add (hb.integrable_sq.const_mul 2))
    (fun x => twoScalarPilotVector_norm_sq_le (a x) (b x))
  change (∫ x, ‖twoScalarPilotVector (a x) (b x)‖ ^ 2 ∂μ) ≤
    (∫ x, 3 * a x ^ 2 + 2 * b x ^ 2 ∂μ) at h
  rw [integral_add (f := fun x => 3 * a x ^ 2) (g := fun x => 2 * b x ^ 2)
    (ha.integrable_sq.const_mul 3) (hb.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  linarith only [h, hEa, hEb]
end
theorem twoScalarPilotVector_measurable {Ω : Type*} [MeasurableSpace Ω]
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => twoScalarPilotVector (a x) (b x)) :=
  ((ha.sub hb).smul measurable_const).sub (ha.smul measurable_const)
theorem twoScalarPilotVector_test_second_le
     [MeasurableSpace Ω] [MeasurableSpace W]
    (μ : Measure Ω) (M : Measure W) (a b : Ω → W → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hinta : ∀ v : W → ℝ, MemLp v 2 M → ∀ x, Integrable (fun w => v w * a x w) M)
    (hintb : ∀ v : W → ℝ, MemLp v 2 M → ∀ x, Integrable (fun w => v w * b x w) M)
    (hLa : ∀ v : W → ℝ, MemLp v 2 M →
      MemLp (fun x => ∫ w, v w * a x w ∂M) 2 μ)
    (hLb : ∀ v : W → ℝ, MemLp v 2 M →
      MemLp (fun x => ∫ w, v w * b x w ∂M) 2 μ)
    (hEa : ∀ v : W → ℝ, MemLp v 2 M →
      (∫ x, (∫ w, v w * a x w ∂M) ^ 2 ∂μ) ≤ c * ∫ w, v w ^ 2 ∂M)
    (hEb : ∀ v : W → ℝ, MemLp v 2 M →
      (∫ x, (∫ w, v w * b x w ∂M) ^ 2 ∂μ) ≤ c * ∫ w, v w ^ 2 ∂M)
    (v : W → PairVector) (hv : MemLp v 2 M) :
    (∫ x, PilotFields.test (M := M) (fun x w => twoScalarPilotVector (a x w) (b x w)) v x ^ 2 ∂μ) ≤
      6 * c * ∫ w, ‖v w‖ ^ 2 ∂M := by
  have h_pairVector_coordinate_memLp (i : Fin 3) : MemLp (fun w => v w i) 2 M := by
    apply hv.mono ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_aestronglyMeasurable hv.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun w => PiLp.norm_apply_le (v w) i
  let vA (w : W) := v w 1 - v w 2
  let vB (w : W) := v w 1
  have hvA : MemLp vA 2 M := (h_pairVector_coordinate_memLp 1).sub (h_pairVector_coordinate_memLp 2)
  have hvB : MemLp vB 2 M := h_pairVector_coordinate_memLp 1
  let A (x : Ω) := ∫ w, vA w * a x w ∂M
  let B (x : Ω) := ∫ w, vB w * b x w ∂M
  have hA : MemLp A 2 μ := hLa vA hvA
  have hB : MemLp B 2 μ := hLb vB hvB
  have heq (x : Ω) : PilotFields.test (M := M)
      (fun x w => twoScalarPilotVector (a x w) (b x w)) v x = A x - B x := by
    unfold PilotFields.test
    simp_rw [twoScalarPilotVector_inner]
    exact integral_sub (hinta vA hvA x) (hintb vB hvB x)
  have hsq := integral_mono (hA.sub hB).integrable_sq
    ((hA.integrable_sq.const_mul 2).add (hB.integrable_sq.const_mul 2))
    (fun x => show (A x - B x) ^ 2 ≤ 2 * A x ^ 2 + 2 * B x ^ 2 by
      nlinarith only [sq_nonneg (A x + B x)])
  change (∫ x, (A x - B x) ^ 2 ∂μ) ≤ (∫ x, 2 * A x ^ 2 + 2 * B x ^ 2 ∂μ) at hsq
  rw [integral_add (f := fun x => 2 * A x ^ 2) (g := fun x => 2 * B x ^ 2)
    (hA.integrable_sq.const_mul 2) (hB.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at hsq
  have hweights : (∫ w, vA w ^ 2 + vB w ^ 2 ∂M) ≤ 3 * ∫ w, ‖v w‖ ^ 2 ∂M := by
    have hp (w : W) : vA w ^ 2 + vB w ^ 2 ≤ 3 * ‖v w‖ ^ 2 := by
      have hn : ‖v w‖ ^ 2 = v w 0 ^ 2 + v w 1 ^ 2 + v w 2 ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ, add_assoc]
      rw [hn]
      dsimp [vA, vB]
      nlinarith only [sq_nonneg (v w 1 + v w 2), sq_nonneg (v w 0), sq_nonneg (v w 2)]
    have hh := integral_mono (hvA.integrable_sq.add hvB.integrable_sq)
      (hv.norm.integrable_sq.const_mul 3) hp
    rwa [integral_const_mul] at hh
  rw [integral_add hvA.integrable_sq hvB.integrable_sq] at hweights
  simp_rw [heq]
  nlinarith only [hsq, hEa vA hvA, hEb vB hvB, mul_le_mul_of_nonneg_left hweights hc]
def paperAllocatedPilotBudget  (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicMultilevelBudget (dyadicSeriesEnvelope C A ((threeBlockSize n ) / 2)
    (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
    (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n))
    (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
    (paperAllocatedFinestLevel C (C₀ * C_D) n)
theorem paperAllocatedPilotBudget_nonneg {d : ℕ} (C : ModelConstants d)
    (A C₀ C_D : ℝ) (n : ℕ) : 0 ≤ paperAllocatedPilotBudget C A C₀ C_D n := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)
theorem paperAllocatedPilotBudget_tends_zero  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (A C₀ C_D )
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    Tendsto (paperAllocatedPilotBudget C A C₀ C_D) atTop (𝓝 0) := by
  have h_eventually_paperAllocatedPilotBudget_le_scalar : ∀ᶠ n : ℕ in atTop,
      paperAllocatedPilotBudget C A C₀ C_D n ≤
      actualAllocationVarianceRatio (paperDyadicStep C) (paperUpperSaddle C) (paperUpperShift C)
        C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) (paperUpperEta C) (paperUpperVarpi C) n := by
    have hH  := mul_pos (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD)
    have hgrid  :=
      tendsto_natCast_atTop_atTop.eventually
        ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.1)
    have h_eventually_paper_dyadic_series_envelope_le (a) (offset) (ha : 0 < a) (hC : 0 < C₀) (hD : 0 < C_D) : ∀ᶠ n : ℕ in atTop,
        dyadicSeriesEnvelope C A ((threeBlockSize n ) / 2)
          (paperDyadicTerminalLevel C a offset (C₀ * C_D) n)
          (paperDyadicApproximationDegree C a offset (C₀ * C_D) n) ≤
        actualVarianceMaximum (paperDyadicStep C) a offset C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) n := by
      have hwidth  :=
        tendsto_natCast_atTop_atTop.eventually
          ((allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop 0))
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_paper_total_degree_eq_floor C hreg.1 a offset (C₀ * C_D) ha), hwidth, eventually_ge_atTop 6] with n hd hS h6
      have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hΛ : (n : ℝ) / 12 ≤ (threeBlockSize n : ℝ) / 2 := by linarith [threeBlockSize_fraction h6]
      have hm : threeBlockSize n ≤ n := by unfold threeBlockSize; omega
      have : (threeBlockSize n : ℝ) ≤ n := by exact_mod_cast hm
      apply Finset.sup'_le
      intro j _
      apply (paper_pilot_series_weight_le_profile C A a offset hn hΛ (by linarith [Nat.cast_nonneg (α := ℝ) (threeBlockSize n)]) hC hD hS hcoef j.val (hd j.val)).trans
      exact Finset.le_sup' (s := Finset.range
        (terminalAllocationLevel (paperDyadicStep C) a offset (C₀ * C_D) (paperDegreeReserve C) n + 1))
        (b := j.val) (fun i => profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
          (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n i)) (Finset.mem_range.mpr j.isLt)
    filter_upwards [h_eventually_paper_dyadic_series_envelope_le (paperUpperSaddle C) (paperUpperShift C) (paperUpperSaddle_pos C hreg) (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD), hgrid] with n hseries hside
    have hround := (dyadicRoundedSide_bounds hside).2
    have hsquare := pow_le_pow_left₀ (Real.exp_pos _).le hround 2
    have hj : (2 ^ paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) ^ 2 =
        Real.exp (2 / d * (Real.log n + paperAllocatedDepth C (C₀ * C_D) n)) := by
      rw [paperAllocatedDepth_eq_level]
      have : d ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
      have he : 2 / d * (Real.log n +
          (paperDyadicStep C * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n : ℝ) - Real.log n)) =
        (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n : ℝ) * Real.log 2 * 2 := by
        unfold paperDyadicStep
        field_simp
        ring
      rw [he]
      have hJ : Real.exp ((paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n : ℝ) * Real.log 2) =
          2 ^ paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [← hJ]
      simpa only [Nat.cast_ofNat, mul_comm] using (Real.exp_nat_mul
        ((paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n : ℝ) * Real.log 2) 2).symm
    have hscale : (paperAllocatedSide C (C₀ * C_D) n) ^ 2 *
        (2 ^ paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) ^ 2 ≤
        Real.exp (-2 * paperUpperVarpi C * Real.log n + paperUpperEta C * paperAllocatedDepth C (C₀ * C_D) n) := by
      calc
        _ ≤ (Real.exp (paperAllocatedLogSide C (C₀ * C_D) n)) ^ 2 *
          (2 ^ paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) ^ 2 :=
            mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
        _ = _ := by
          rw [hj, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          simpa only [paperAllocatedLogSide, Nat.cast_ofNat, mul_comm _ ↑2] using
            paper_spatial_reserve_identity C hreg (Real.log n) (paperAllocatedDepth C (C₀ * C_D) n)
    change _ ≤ Real.exp _ * _
    unfold paperAllocatedPilotBudget dyadicMultilevelBudget
    rw [paperAllocatedFinestLevel, ← dyadicRoundedSide_eq_inv_pow]
    exact mul_le_mul hscale hseries
      (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)
      (Real.exp_pos _).le
  apply squeeze_zero' (Filter.Eventually.of_forall (paperAllocatedPilotBudget_nonneg C A C₀ C_D))
    h_eventually_paperAllocatedPilotBudget_le_scalar
  exact (actualAllocationVarianceRatio_tends_zero (paperDyadicStep_pos C) (paperUpperSaddle_pos C hreg)
    hC hD hDβ (paperDegreeSlope_pos C hreg.1) (paperDegreeReserve_pos C hreg.1).le
    (paperUpperEta_pos C).le (paperUpperShift C) rfl
    (paper_upper_saddle_budget_identity C hreg)).comp tendsto_natCast_atTop_atTop
theorem eventually_paperAllocatedPilotBudget_le_one {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (A C₀ C_D : ℝ)
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, paperAllocatedPilotBudget C A C₀ C_D n ≤ 1 :=
  ((paperAllocatedPilotBudget_tends_zero C hreg A C₀ C_D hC hD hDβ hcoef).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
theorem pairPilotAssumptions_of_two_scalars
     [MeasurableSpace Ω] (μ ) [IsFiniteMeasure μ] 
    (θ k hk bar)
    (a b : Ω → Covariate d × Covariate d → ℝ)
    {Cp W point test Λ : ℝ} (hCp : 0 ≤ Cp) (hW : 0 ≤ W)
    (htest : 0 ≤ test) (hΛ : 0 < Λ) (hpoint : 5 * point ≤ Cp)
    (hmbar : Measurable bar)
    (hma : Measurable (fun z : Ω × (Covariate d × Covariate d) => a z.1 z.2))
    (hmb : Measurable (fun z : Ω × (Covariate d × Covariate d) => b z.1 z.2))
    (hbar : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp)
    (hsections : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => a x w) 2 μ ∧ MemLp (fun x => b x w) 2 μ)
    (henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, a x w ^ 2 ∂μ) ≤ point * W ∧ (∫ x, b x w ^ 2 ∂μ) ≤ point * W)
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      (∫ x, a x w ∂μ) = 0 ∧ (∫ x, b x w ∂μ) = 0)
    (hinta : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * a x w) (regularPairDesignMeasure θ k hk))
    (hintb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * b x w) (regularPairDesignMeasure θ k hk))
    (hLa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hLb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hEa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hEb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk) :
    PairPilotAssumptions θ k hk μ bar (fun x w => twoScalarPilotVector (a x w) (b x w))
      Cp W (6 * (test * W / Λ)) := by
  refine ⟨hCp, hW, hmbar, twoScalarPilotVector_measurable hma hmb, hbar, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hsections] with w hw hs
    exact twoScalarPilotVector_memLp (hw hs).1 (hw hs).2
  · filter_upwards [hsections, henergy] with w hw he hs
    exact (twoScalarPilotVector_second_le (hw hs).1 (hw hs).2 (he hs).1 (he hs).2).trans
      (by have hm := mul_le_mul_of_nonneg_right hpoint hW; nlinarith only [hm])
  · have hM := regularPairDesignMeasure_ae_of_supported θ k hk hsections
    filter_upwards [hM, hcenter] with w hw hc
    exact twoScalarPilotVector_mean_zero hw.1 hw.2 hc.1 hc.2
  · positivity
  · intro v hv
    exact twoScalarPilotVector_test_second_le μ (regularPairDesignMeasure θ k hk) a b
      (div_nonneg (mul_nonneg htest hW) hΛ.le) hinta hintb hLa hLb hEa hEb v hv
theorem PairPilotAssumptions.mono_lam  [MeasurableSpace Ω] 
      {hk : 0 < k} {μ : Measure Ω}
    {bar : Covariate d × Covariate d → PairVector}
    {η : Ω → Covariate d × Covariate d → PairVector} {Cp W lam lam' : ℝ}
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam) (hl : lam ≤ lam') :
    PairPilotAssumptions θ k hk μ bar η Cp W lam' := by
  refine { hp with lamNonnegative := hp.lamNonnegative.trans hl, linearTest := ?_ }
  intro v hv
  exact (hp.linearTest v hv).trans (mul_le_mul_of_nonneg_right hl
    (integral_nonneg (fun w => sq_nonneg ‖v w‖)))
theorem uniform_domain_dyadic_pair_pilot_assumptions  (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ A Cp, 0 < A ∧ 0 < Cp ∧
      ∀ U, ∀ θ, Admissible (C.withDomain U) θ →
      ∀ (n : ℝ), 0 < n → ∀ N J L : ℕ, J ≤ L → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ N) →
      ∀ Λ : ℝ, 0 < Λ → n / 12 ≤ Λ →
      (∀ j : Fin (J + 1), Λ ≤ (N : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      PairPilotAssumptions θ ((2 : ℕ) ^ L) (by positivity) (sampleLaw θ N)
        (dyadicPopulationCoefficients C θ J m)
        (fun z w => twoScalarPilotVector (dyadicMultilevelErrorField C θ N J 0 m z w)
          (dyadicMultilevelErrorField C θ N J 1 m z w))
        Cp (dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L)
        (Cp ^ 2 * dyadicMultilevelBudget
          (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / n) := by
  letI : Nonempty (AnchoredIndex d C.order) := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨D, A, hD, hA, hb⟩ := uniform_domain_common_dyadicMultilevel_bounds C
  obtain ⟨Cp₀, hCp₀, hbar⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hs
  let point : ℝ := 4 * ((anchoredDimension d C.order ) * D) ^ 2 * d
  let test : ℝ := 4 * C.densityUpper ^ 2 * 2 ^ d *
    ((anchoredDimension d C.order ) * D) ^ 2 * d
  let Cp : ℝ := max Cp₀ (max 1 (5 * point + 72 * test + 1))
  have hp0 : 0 ≤ point := by dsimp [point]; positivity
  have ht0 : 0 ≤ test := by dsimp [test]; positivity
  have hC1 : 1 ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hCall : 5 * point + 72 * test + 1 ≤ Cp := (le_max_right _ _).trans (le_max_right _ _)
  have hCp : 0 < Cp := zero_lt_one.trans_le hC1
  have hc : 72 * test ≤ Cp := by linarith only [hCall, hp0]
  have hsq : Cp ≤ Cp ^ 2 := by nlinarith only [hC1]
  have htest := hc.trans hsq
  refine ⟨A, Cp, hA, hCp, ?_⟩
  intro U θ hθ n hn N J L hJL m hdegree Λ hΛ hΛn hΛdegree
  let CU := C.withDomain U
  letI : Nonempty (AnchoredIndex d CU.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  let := sampleLaw_isProbability CU θ hθ N
  let := designLaw_isProbability CU θ hθ
  let W := dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (dyadicSeriesEnvelope_nonneg _ _ _ hΛ.le _ _)
  have hy0 : |(0 : ℝ)| ≤ max C.holderBound 1 := by
    simpa only [abs_zero] using (zero_le_one.trans (le_max_right C.holderBound 1))
  have hy1 : |1| ≤ max C.holderBound 1 := by simpa only [abs_one] using le_max_right C.holderBound 1
  have hbounds y (hy : |y| ≤ max C.holderBound 1) :=
    hb U θ hθ N J L hJL y hy m hdegree Λ hΛ hΛdegree
  have hcubes : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ), w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ), (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hz
    exact ⟨hx, hz⟩
  have hf y (w : Covariate d × Covariate d) (hx : w.1 ∈ unitCube d) :=
    dyadicMultilevelErrorField_point_moment_facts CU θ hθ N J w.1 hx w.2 y m hdegree
  have henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell (2 ^ L) (by positivity)) w ≠ 0 →
        (∫ z, dyadicMultilevelErrorField C θ N J 0 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W ∧
        (∫ z, dyadicMultilevelErrorField C θ N J 1 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W := by
    filter_upwards [hcubes] with w hw hs
    have hc : regularGridCell (2 ^ L) (by positivity) w.1 =
        regularGridCell (2 ^ L) (by positivity) w.2 := by
      by_contra h
      apply hs
      simp [sameLabelKernel, h]
    exact ⟨(hbounds 0 hy0).1 w.1 hw.1 w.2 hw.2 hc,
      (hbounds 1 hy1).1 w.1 hw.1 w.2 hw.2 hc⟩
  have hp := pairPilotAssumptions_of_two_scalars (sampleLaw θ N) θ (2 ^ L) (by positivity)
    (dyadicPopulationCoefficients C θ J m)
    (dyadicMultilevelErrorField C θ N J 0 m) (dyadicMultilevelErrorField C θ N J 1 m)
    hCp.le hW ht0 hΛ (by linarith only [hCall, ht0])
    (dyadicPopulationCoefficients_measurable CU θ hθ J m)
    (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 0 m hdegree)
    (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 1 m hdegree)
    ((hbar U θ hθ J L hJL m).mono (fun _ hw hs => (hw hs).trans (le_max_left _ _)))
    (by filter_upwards [hcubes] with w hw _; exact ⟨(hf 0 w hw.1).1, (hf 1 w hw.1).1⟩) henergy (by filter_upwards [regularPairDesignMeasure_cube_ae CU θ hθ ((2 : ℕ) ^ L) (by positivity)] with w hw; exact ⟨(hf 0 w hw.1).2, (hf 1 w hw.1).2⟩)
    (dyadicMultilevelErrorField_envelope_weighted_integrable CU θ hθ N J L hJL 0 hy0 m hdegree)
    (dyadicMultilevelErrorField_envelope_weighted_integrable CU θ hθ N J L hJL 1 hy1 m hdegree)
    (fun v hv => (dyadicMultilevelErrorField_envelope_test_moment_facts CU θ hθ N J L hJL 0 hy0 m hdegree v hv).1)
    (fun v hv => (dyadicMultilevelErrorField_envelope_test_moment_facts CU θ hθ N J L hJL 1 hy1 m hdegree v hv).1)
    (hbounds 0 hy0).2 (hbounds 1 hy1).2
  exact hp.mono_lam (by rw [← mul_div_assoc]; apply (div_le_div_iff₀ ((div_pos hn (by norm_num)).trans_le hΛn) hn).mpr; have hmn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htest hW) hn.le; nlinarith only [hmn, mul_le_mul_of_nonneg_left hΛn (mul_nonneg (sq_nonneg Cp) hW)])
def paperUpperRootReserve  (C : ModelConstants d) : ℝ :=
  (d - 4 * C.smoothness) / (4 * (d + 4))
def paperAllocatedMasterConstant  (C : ModelConstants d) (B : ℝ) : ℝ :=
  B ^ 2 * d + 2 * (1 + Real.exp (d / 2 * Real.log 2))
section
def polynomialLiftLinearMap  
    (X : Fin n → Ω → Fin p → ℝ) (z : Ω) : MvPolynomial (Fin p) ℝ →ₗ[ℝ] ℝ where
  toFun P := Finsupp.linearCombination ℝ (fun α =>
    RoughRegime.Upper.monomialLift (RoughRegime.Upper.exponentCoordinates α) X z) P.coeff
  map_add' P Q := by simp only [AddMonoidAlgebra.coeff_add, map_add]
  map_smul' a P := by simp only [AddMonoidAlgebra.coeff_smul, map_smul, RingHom.id_apply]
theorem polynomialLiftLinearMap_apply {Ω : Type*} {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (z : Ω) (P : MvPolynomial (Fin p) ℝ) :
    polynomialLiftLinearMap X z P = RoughRegime.Upper.polynomialLift P X z := by
  simp only [polynomialLiftLinearMap, Finsupp.linearCombination_apply, Finsupp.sum,
    smul_eq_mul, RoughRegime.Upper.polynomialLift, MvPolynomial.finsupp_support_eq_support]
  rfl
theorem polynomialLift_joint_measurable  [MeasurableSpace Ω] {n p : ℕ}
    (P : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (RoughRegime.Upper.polynomialLift P X) := by
  apply Finset.measurable_sum
  intro α _
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  exact Finset.measurable_prod Finset.univ (fun i _ => (hX (e i)).eval)
theorem rowIncrementPolynomial_lift  {n r : ℕ}
    (a b T y m)
    (row : Fin r → ℝ)
    (X : Fin n → Ω → Fin (Fintype.card (incrementVariables r)) → ℝ) (z : Ω) :
    RoughRegime.Upper.polynomialLift (rowIncrementPolynomial r a b T y m row) X z =
      ∑ i, row i * RoughRegime.Upper.polynomialLift (incrementFinPolynomial r a b T y m i) X z := by
  simp only [← polynomialLiftLinearMap_apply, rowIncrementPolynomial, ← MvPolynomial.smul_eq_C_mul,
    map_sum, map_smul, smul_eq_mul]
attribute [local irreducible] dyadicIncrementRawVector
set_option backward.isDefEq.respectTransparency true in
theorem dyadicPolynomialPilot_raw_joint_measurable  (C : ModelConstants d)
    (n j y m row)
    (hrow : Measurable row) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1) := by
  have hX (i : Fin n) : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicIncrementRawVector (d := d) (ℓ := C.order) j t.2.1 (t.1 i)) := by
    have hmarg : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
        (t.2.1, t.1 i)) :=
      (measurable_fst.comp measurable_snd).prodMk ((measurable_pi_apply i).comp measurable_fst)
    exact (dyadicIncrementRawVector_joint_measurable (d := d) (ℓ := C.order) j).comp hmarg
  let X : Fin n → (Fin n → Observation d) × (Covariate d × Covariate d) →
      Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ :=
    fun i t => dyadicIncrementRawVector (d := d) (ℓ := C.order) j t.2.1 (t.1 i)
  have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1) =
      (fun t => ∑ i, row t.2 i * RoughRegime.Upper.polynomialLift
        (incrementFinPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m i) X t) := by
    funext t
    simp only [dyadicPolynomialPilot, rowIncrementPolynomial_lift]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact ((hrow.eval (a := i)).comp measurable_snd).mul
    (polynomialLift_joint_measurable (n := n)
      (p := Fintype.card (incrementVariables (anchoredDimension d C.order))) _ X hX)
def dyadicRawPilotSum  (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (y : ℝ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPolynomialPilot C n j.val w.1 y (m j.val)
    (dyadicPilotRow j.val w.1 w.2) z
def dyadicRawCoefficients  (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + (dyadicRawPilotSum C n J m 0 z w - dyadicRawPilotSum C n J m 1 z w),
    -dyadicRawPilotSum C n J m 0 z w]
def dyadicNoiseCoefficients  (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (m : ℕ → ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : PairVector :=
  twoScalarPilotVector (dyadicMultilevelErrorField C θ n J 0 m z w)
    (dyadicMultilevelErrorField C θ n J 1 m z w)
theorem dyadicRawPilotSum_joint_measurable  (C n J m y) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicRawPilotSum C n J m y t.1 t.2) :=
  Finset.measurable_sum Finset.univ (fun j _ =>
    dyadicPolynomialPilot_raw_joint_measurable C n j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val))
theorem dyadicMultilevelErrorField_eq_raw_sub_population {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (n J : ℕ) (m : ℕ → ℕ) (y : ℝ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) :
    dyadicMultilevelErrorField C θ n J y m z w = dyadicRawPilotSum C n J m y z w -
      (dyadicPopulationPilotSum C θ J m false w - y * dyadicPopulationPilotSum C θ J m true w) := by
  unfold dyadicMultilevelErrorField dyadicPilotErrorField dyadicRawPilotSum
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold dyadicPopulationPilotSum
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [incrementFinScalar, incrementFinVector_affine]
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dyadicPopulationRawPolynomial, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem dyadicRawCoefficients_eq_population_add_noise {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (n J : ℕ) (m : ℕ → ℕ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) :
    dyadicRawCoefficients C n J m z w = dyadicPopulationCoefficients C θ J m w +
      dyadicNoiseCoefficients C θ n J m z w := by
  ext i
  fin_cases i <;>
    simp [dyadicRawCoefficients, dyadicPopulationCoefficients, dyadicNoiseCoefficients,
      twoScalarPilotVector_coordinates, dyadicMultilevelErrorField_eq_raw_sub_population] <;> ring
end
theorem polynomial_bounds_nat_of_rateBracket {risk : ℕ → ℝ} {lam kappa a Gamma : ℝ}
    (hk : 0 < kappa) (h : HasNatRateBracket risk lam kappa a Gamma) :
    ∃ c A, 0 < c ∧ 0 < A ∧ ∀ epsilon, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*n^(-lam-epsilon) ≤ risk n ∧ risk n ≤ A*n^(-lam) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  refine ⟨c,A,hc,hA,fun epsilon he => ?_⟩
  have h_eventually_correction_between_powers {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop,
      x ^ (-ε) ≤ Real.exp (-kappa * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ∧
      Real.exp (-kappa * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ≤ x ^ ε := by
    have h := tendsto_correction_div_log kappa a
    filter_upwards [h.eventually (lt_mem_nhds (neg_lt_zero.2 hε)),
      h.eventually (gt_mem_nhds hε), eventually_gt_atTop ↑1] with x hlo hhi hx
    have hl  := Real.log_pos hx
    have hx₀ : 0 < x := by linarith
    rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hx₀]
    constructor
    · apply Real.exp_le_exp.2
      have := (lt_div_iff₀ hl).1 hlo
      linarith
    · apply Real.exp_le_exp.2
      have := (div_lt_iff₀ hl).1 hhi
      linarith
  filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually
    (h_eventually_correction_between_powers he),
    tendsto_natCast_atTop_atTop.eventually
      ((tendsto_stretched_log_factor hk (a+Gamma)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  constructor
  · apply le_trans _ hn.1
    rw [rateScale_eq_base_mul_correction]
    have hr : (n : ℝ)^(-lam-epsilon) = Real.exp (-lam*Real.log n)*(n : ℝ)^(-epsilon) := by
      rw [Real.rpow_def_of_pos hn0,Real.rpow_def_of_pos hn0,←Real.exp_add]
      congr 1
      ring
    rw [hr]
    simp only [←mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow.1 (mul_pos hc (Real.exp_pos _)).le
  · apply le_trans hn.2
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0, mul_comm (Real.log (n : ℝ)) (-lam)]
    calc
      _ ≤ A*(Real.exp (-lam*Real.log n)*1) := by gcongr
      _ = _ := by ring
theorem paper_main {d : ℕ} (C : ModelConstants d) : MainBracketClaim C :=
  have h_mainBracketClaim_of_separate_bounds : MainBracketClaim C := by
    have h_paperUpperRiskDepthCoefficient_pos (hs : 1 < C.smoothness) : 0 < paperUpperRiskDepthCoefficient C := div_pos (mul_pos (by norm_num) (sub_pos.mpr hs)) (by positivity)
    have h_paperUpperRootReserve_pos (hreg : highSmoothnessRegime C) : 0 < paperUpperRootReserve C := div_pos (sub_pos.mpr hreg.2) (mul_pos (by norm_num) (by positivity))
    have h_paperAllocatedMasterConstant_pos (B : ℝ) : 0 < paperAllocatedMasterConstant C B := by
      unfold paperAllocatedMasterConstant
      positivity
    have h_paper_upper_sharp : UpperSharpClaim C := by
      intro hreg
      have h_paper_upper_sharp_estimator : ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
          ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n → ∃ T : Estimator d n,
            ∀ θ, Admissible (C.withDomain U) θ →
              meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
        have h_uniform_domain_eventually_allocated_pair_pilot_assumptions : ∃ A Cp : ℝ, 0 < A ∧ 0 < Cp ∧ ∀ C₀ C_D : ℝ, 0 < C₀ → 0 < C_D →
            ∀ᶠ n : ℕ in atTop, ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d,
            Admissible (C.withDomain U) θ →
            PairPilotAssumptions θ ((2 : ℕ) ^ paperAllocatedFinestLevel C (C₀ * C_D) n)
              (by positivity) (sampleLaw θ (threeBlockSize n))
              (dyadicPopulationCoefficients C θ
                (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
                (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n))
              (fun z w => twoScalarPilotVector
                (dyadicMultilevelErrorField C θ (threeBlockSize n)
                  (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
                  0 (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) z w)
                (dyadicMultilevelErrorField C θ (threeBlockSize n)
                  (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
                  1 (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) z w))
              Cp (paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n)
              (Cp ^ 2 * paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n / (n : ℝ)) := by
          obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_dyadic_pair_pilot_assumptions C hreg.1
          refine ⟨A, Cp, hA, hCp, ?_⟩
          intro C₀ C_D hC hD
          have hH  := mul_pos hC hD
          have hg  :=
            tendsto_natCast_atTop_atTop.eventually
              ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2)
          filter_upwards [hg, eventually_paper_degree_three_block_guards C hreg.1
            (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) (paperUpperSaddle_pos C hreg) hH,
            eventually_ge_atTop (6 : ℕ)] with n hg hdeg h6
          intro U θ hθ
          let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n
          let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n
          have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
          have hΛ  := (hdeg 0 (Nat.zero_le _)).2.1
          have hΛn : (n : ℝ) / 12 ≤ (threeBlockSize n : ℝ) / 2 := by
            have hf := threeBlockSize_fraction h6
            linarith only [hf, hn]
          have hd (j : Fin (J + 1)) : m j.val + anchoredDimension d C.order + 1 ≤ threeBlockSize n :=
            (hdeg j.val (Nat.le_of_lt_succ j.isLt)).1
          have hΛd (j : Fin (J + 1)) : (threeBlockSize n : ℝ) / 2 ≤ (threeBlockSize n : ℝ) -
              (m j.val + anchoredDimension d C.order + 1) + 1 := by
            simpa only [paperDyadicTotalDegree, Nat.cast_add, Nat.cast_one, m] using
              (hdeg j.val (Nat.le_of_lt_succ j.isLt)).2.2
          exact hp U θ hθ n hn (threeBlockSize n) J
            (paperAllocatedFinestLevel C (C₀ * C_D) n) hg m hd
            ((threeBlockSize n : ℝ) / 2) hΛ hΛn hΛd
        obtain ⟨A, Cp, hA, hCp, hp⟩ := h_uniform_domain_eventually_allocated_pair_pilot_assumptions
        let C₀ := max 1 (12 * paperPilotMomentFactor (pilotModelConstants C) A)
        let C_D := max 1 (4 * paperDegreeSlope C)
        have hC : 1 ≤ C₀ := le_max_left _ _
        have hD : 1 ≤ C_D := le_max_left _ _
        have hCpos : 0 < C₀ := zero_lt_one.trans_le hC
        have hDpos : 0 < C_D := zero_lt_one.trans_le hD
        have hDβ : 4 * paperDegreeSlope (pilotModelConstants C) ≤ C_D := le_max_right _ _
        have hcoef : 12 * paperPilotMomentFactor (pilotModelConstants C) A ≤ C₀ := le_max_right _ _
        let H := C₀ * C_D
        have hH : 0 < H := mul_pos hCpos hDpos
        obtain ⟨_, B, _, hB, hpop⟩ := uniform_domain_allocated_population_pair_witnesses C hreg hH
        have h_paper_allocated_risk_scale_upper : ∃ A, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
            paperAllocatedRiskScale C H n ≤ A * paperUpperScale C n := by
          have h_paper_allocated_risk_scale_bracket : ∃ A B, 0 < A ∧ 0 < B ∧ ∀ᶠ x : ℝ in atTop,
              A * Real.exp (-rateExponent C.smoothness d * Real.log x -
                stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log x) +
                (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)) ≤
                  paperAllocatedRiskScale C H x ∧
              paperAllocatedRiskScale C H x ≤ B * Real.exp (-rateExponent C.smoothness d * Real.log x -
                stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log x) +
                (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)) := by
            obtain ⟨A, B, hA, hB, hb⟩ := rounded_upper_saddle_scale_bracket
              (paperUpperSaddle_pos C hreg) hH (paperDyadicStep_pos C)
              (paperUpperShift C) (paperDegreeReserve C) (rateExponent C.smoothness d)
              (h_paperUpperRiskDepthCoefficient_pos hreg.1).le
            refine ⟨A, B, hA, hB, ?_⟩
            have h_paper_upper_log_power_identity : paperUpperRiskDepthCoefficient C * (1 + paperDegreeReserve C) / 2 =
                lowerLogPower C.smoothness d + paperLogGap C := by
              have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
              have hdp : (d : ℝ) + 4 ≠ 0 := by positivity
              have hs0  := (sub_pos.mpr hreg.1).ne'
              have hq : 1 ≤ (d + C.order).choose d := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
              have hcard : (anchoredDimension d C.order : ℝ) = (paperPolynomialDimension C : ℝ) - 1 := by
                unfold anchoredDimension paperPolynomialDimension
                rw [anchoredIndex_card, Nat.cast_sub hq, Nat.cast_one]
              unfold paperUpperRiskDepthCoefficient paperDegreeReserve paperSpatialExponent lowerLogPower paperLogGap
              rw [hcard]
              field_simp
              ring
            have h_paper_upper_stretch_identity : paperUpperRiskDepthCoefficient C * paperUpperSaddle C =
                stretchConstant C.smoothness d (paperTau C) := upper_saddle_stretchConstant hreg.1 hreg.2 (paperTau_pos C)
            simpa only [paperAllocatedRiskScale, paperAllocatedDepth, ← mul_assoc,
              h_paper_upper_stretch_identity, h_paper_upper_log_power_identity] using hb
          obtain ⟨_, A, _, hA, ha⟩ := h_paper_allocated_risk_scale_bracket
          refine ⟨A, hA, ?_⟩
          filter_upwards [tendsto_natCast_atTop_atTop.eventually ha, eventually_ge_atTop 2] with n hn hn2
          rw [paperUpperScale_eq_rateScale C hn2]
          exact hn.2
        obtain ⟨S, hS, hscale⟩ := h_paper_allocated_risk_scale_upper
        let K := Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
          paperAllocatedMasterConstant C B * S
        have hK : 0 < K := mul_pos (mul_pos
          (Real.sqrt_pos.mpr (pairRateSquaredConstant_pos C hCp.le (by norm_num) (by norm_num)))
          (h_paperAllocatedMasterConstant_pos B)) hS
        have hW := eventually_paperAllocatedPilotBudget_le_one (pilotModelConstants C)
          hreg A C₀ C_D hC hD hDβ hcoef
        have hall : ∀ᶠ n : ℕ in atTop, ∀ U : ExtensionDomain d,
            ∃ T : Estimator d n, ∀ θ, Admissible (C.withDomain U) θ →
              meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
          have h_eventually_paper_allocated_master_rate : ∀ᶠ n : ℕ in atTop, ∀ W, 0 ≤ W → W ≤ 1 →
              (B * Real.sqrt d * paperAllocatedSide C H n *
                (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
                  (-paperSpatialExponent C)) ^ 2 +
                pairFluctuationScale (d := d) n (2 ^ paperAllocatedFinestLevel C H n) * (1 + W) ≤
              paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n := by
            have hg := tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard C hreg hH)
            have h_eventually_paper_allocated_fluctuation_bound : ∀ᶠ n : ℕ in atTop,
                pairFluctuationScale (d := d) n (2 ^ paperAllocatedFinestLevel C H n) ≤
                  (1 + Real.exp (d / 2 * Real.log 2)) * paperAllocatedRiskScale C H n := by
              have hg := tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard C hreg hH)
              have h_eventually_paper_allocated_root_noise_bound : ∀ᶠ x : ℝ in atTop, Real.exp (-Real.log x / 2) ≤
                Real.exp (-paperUpperRootReserve C * Real.log x) * paperAllocatedRiskScale C H x := by
                have hlim := tendsto_sqrt_log_div_log.const_mul
                  (paperUpperRiskDepthCoefficient C * paperUpperSaddle C)
                simp only [mul_zero] at hlim
                filter_upwards [hlim.eventually (gt_mem_nhds (h_paperUpperRootReserve_pos hreg)),
                  eventually_paper_allocated_depth_le_width C hreg hH,
                  Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hx hT hL
                have hchi := h_paperUpperRiskDepthCoefficient_pos hreg.1
                have hbeta := paperDegreeSlope_pos C hreg.1
                have hshift : 0 ≤ paperUpperShift C := by
                  exact add_nonneg (by norm_num) (div_nonneg
                    (mul_nonneg (by norm_num) (by linarith only [paperUpperEta_pos C])) hbeta.le)
                have hS : allocationWidth (paperUpperSaddle C) (paperUpperShift C) x ≤
                    paperUpperSaddle C * Real.sqrt (Real.log x) := by
                  unfold allocationWidth
                  linarith only [hshift]
                have hm := mul_le_mul_of_nonneg_left (hT.trans hS) hchi.le
                have hsmall : paperUpperRiskDepthCoefficient C * paperUpperSaddle C * Real.sqrt (Real.log x) ≤
                    paperUpperRootReserve C * Real.log x := by
                  rw [← mul_div_assoc] at hx
                  exact ((div_lt_iff₀ hL).mp hx).le
                have hgap : 1 / 2 - rateExponent C.smoothness d = 2 * paperUpperRootReserve C := by
                  rw [half_minus_rateExponent hreg.1 hreg.2]
                  unfold paperUpperRootReserve
                  have : d + 4 ≠ 0 := by positivity
                  field_simp
                  ring
                have hgapL := congrArg (fun t => t * Real.log x) hgap
                unfold paperAllocatedRiskScale
                rw [← Real.exp_add]
                apply Real.exp_le_exp.mpr
                nlinarith only [hm, hsmall, hgapL]
              have hr := tendsto_natCast_atTop_atTop.eventually h_eventually_paper_allocated_root_noise_bound
              filter_upwards [hg, hr, eventually_ge_atTop 1] with n hgrid hroot hn
              have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
              have hr0 : Real.exp (-paperUpperRootReserve C * Real.log n) ≤ 1 :=
                Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (h_paperUpperRootReserve_pos hreg).le) hlog)
              have hR : 0 ≤ paperAllocatedRiskScale C H n := (Real.exp_pos _).le
              have hroot' := hroot.trans (mul_le_mul_of_nonneg_right hr0 hR)
              have h_paper_allocated_pair_noise_bound : Real.exp (-Real.log n - d / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H n)) ≤
                Real.exp (d / 2 * Real.log 2) * paperAllocatedRiskScale C H n := by
                have h := dyadicRounded_noise_bound hgrid.1 (Nat.cast_nonneg d) (Real.log n)
                rw [paperAllocatedLogSide, spatial_balance_rate hreg.1 hreg.2] at h
                exact h
              have hpair := h_paper_allocated_pair_noise_bound
              have h_pairFluctuationScale_dyadic_eq (L : ℕ) : pairFluctuationScale (d := d) n ((2 : ℕ) ^ L) =
                  Real.exp (-Real.log n / 2) +
                    Real.exp (-Real.log n - d / 2 * (-Real.log 2 * L)) := by
                have hn : 0 < n := (by omega)
                have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
                have hroot : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (-Real.log n / 2) := by
                  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR, ← Real.exp_neg]
                  congr 1
                  ring
                have hpair : Real.sqrt ((((2 : ℕ) ^ L : ℕ) : ℝ) ^ d) / (n : ℝ) =
                    Real.exp (-Real.log n - (d : ℝ) / 2 * (-Real.log 2 * (L : ℝ))) := by
                  rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow,
                    Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_pow, show (n : ℝ) = Real.exp (Real.log n) from (Real.exp_log hnR).symm,
                    ← Real.exp_sub, Real.log_exp]
                  congr 1
                  ring
                exact congrArg₂ (· + ·) hroot hpair
              rw [h_pairFluctuationScale_dyadic_eq]
              change _ + Real.exp (-Real.log n - (d : ℝ) / 2 *
                dyadicRoundedLogSide (paperAllocatedLogSide C H n)) ≤ _
              exact (add_le_add hroot' hpair).trans_eq (by ring)
            filter_upwards [hg, h_eventually_paper_allocated_fluctuation_bound] with n hgrid hfl
            intro W hW hW1
            have h_paper_allocated_bias_square_bound : (paperAllocatedSide C H n *
                (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
                  (-paperSpatialExponent C)) ^ 2 ≤ paperAllocatedRiskScale C H n := by
              have hpow := pow_le_pow_left₀ ((Real.exp_pos _).le) ((dyadicRoundedSide_bounds hgrid.1).2) 2
              rw [mul_pow]
              apply (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans_eq
              rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
                ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
              congr 1
              have hdepth : Real.log n + paperAllocatedDepth C H n = paperDyadicStep C *
                  (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n : ℝ) := by
                rw [paperAllocatedDepth_eq_level]
                ring
              have hbalance := spatial_balance hreg.1 hreg.2 (Real.log n) (paperAllocatedDepth C H n)
              have hrate := spatial_balance_rate hreg.1 hreg.2 (Real.log n) (paperAllocatedDepth C H n)
              change _ = -rateExponent C.smoothness d * Real.log n -
                2 * (C.smoothness - 1) / (d + 4) * paperAllocatedDepth C H n
              unfold paperAllocatedLogSide paperSpatialExponent
              rw [hdepth] at hbalance
              nlinarith only [hbalance, hrate]
            have hmul := mul_le_mul_of_nonneg_left h_paper_allocated_bias_square_bound (by positivity : 0 ≤ B ^ 2 * d)
            have hsq : (B * Real.sqrt d * paperAllocatedSide C H n *
                (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
                  (-paperSpatialExponent C)) ^ 2 =
                (B ^ 2 * d) * (paperAllocatedSide C H n *
                  (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
                    (-paperSpatialExponent C)) ^ 2 := by
              simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
              ring
            rw [← hsq] at hmul
            unfold paperAllocatedMasterConstant
            nlinarith only [hmul, (mul_le_mul_of_nonneg_left (show 1 + W ≤ 2 by linarith only [hW1]) (pairFluctuationScale_nonneg (d := d) n (2 ^ paperAllocatedFinestLevel C H n))), hfl]
          filter_upwards [hp C₀ C_D hCpos hDpos, hpop, hscale, hW,
            h_eventually_paper_allocated_master_rate,
            eventually_ge_atTop (6 : ℕ)] with n hpn hpopn hscalen hWn hmastern hn6
          intro U
          let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
          let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
          let L := paperAllocatedFinestLevel C H n
          let k := (2 : ℕ) ^ L
          let W := paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n
          let c := dyadicRawCoefficients C (threeBlockSize n) J m
          have h_dyadicRawCoefficients_joint_measurable (n) : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
              dyadicRawCoefficients C n J m t.1 t.2) := by
            have h0 := dyadicRawPilotSum_joint_measurable C n J m 0
            apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
            apply measurable_pi_iff.mpr
            intro i
            fin_cases i
            · exact measurable_const
            · exact measurable_const.add (h0.sub (dyadicRawPilotSum_joint_measurable C n J m 1))
            · exact h0.neg
          have hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
              (Covariate d × Covariate d) => c z.1 z.2) :=
            (h_dyadicRawCoefficients_joint_measurable _)
          let T := coefficientPairEstimator (C.withDomain U) k (by dsimp only [k]; positivity) c hmc
          refine ⟨T, ?_⟩
          intro θ hθ
          let bar := dyadicPopulationCoefficients C θ J m
          let η := dyadicNoiseCoefficients C θ (threeBlockSize n) J m
          have heq : c = pairPilotCoefficient bar η := by
            funext z w
            exact dyadicRawCoefficients_eq_population_add_noise C θ _ J m z w
          have hpr : PairPilotAssumptions θ k (by dsimp only [k]; positivity)
              (sampleLaw θ (threeBlockSize n)) bar η Cp W (Cp ^ 2 * W / (n : ℝ)) := hpn U θ hθ
          have hpopulation := hpopn U θ hθ
          have hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k (by dsimp only [k]; positivity), bar w 0 = 1 :=
            Filter.Eventually.of_forall hpopulation.2.1
          let b := B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
            (dyadicPilotScale d J) ^ (-paperSpatialExponent C)
          have hr := coefficientPairEstimator_rms_bound (C.withDomain U) θ hθ hn6 k
            (by dsimp only [k]; positivity) c hmc bar η Cp W b heq hpr hfirst hpopulation.2.2.2
          apply hr.trans
          apply ENNReal.ofReal_mono
          have hw0 : 0 ≤ W := paperAllocatedPilotBudget_nonneg (pilotModelConstants C) A C₀ C_D n
          have hm := hmastern W hw0 hWn
          have hPC : 0 ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) := Real.sqrt_nonneg _
          have hMC : 0 ≤ paperAllocatedMasterConstant C B := (h_paperAllocatedMasterConstant_pos B).le
          have h1 := mul_le_mul_of_nonneg_left hm hPC
          have h2 := mul_le_mul_of_nonneg_left hscalen (mul_nonneg hPC hMC)
          calc
            _ ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
                (paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n) := h1
            _ = (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
                paperAllocatedMasterConstant C B) * paperAllocatedRiskScale C H n := by ring
            _ ≤ (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
                paperAllocatedMasterConstant C B) * (S * paperUpperScale C n) := h2
            _ = K * paperUpperScale C n := by dsimp only [K]; ring
        obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
        refine ⟨K, hK, max 2 n₀, le_max_left _ _, ?_⟩
        intro U n hn
        exact hn₀ n ((le_max_right _ _).trans hn) U
      obtain ⟨K, hK, n₀, hn₀, hT⟩ := h_paper_upper_sharp_estimator
      refine ⟨K, hK, n₀, hn₀, ?_⟩
      intro U n hn
      obtain ⟨T, hr⟩ := hT U n hn
      exact minimaxRMS_le_of_estimator_rms (C.withDomain U) T hr
    have hupper  := h_paper_upper_sharp
    have hlower  := (paper_lower_sharp C)
    intro hreg
    obtain ⟨A, hA, nU, hnU, hu⟩ := hupper hreg
    obtain ⟨c, hc, nL, hnL, hl⟩ := hlower hreg
    refine ⟨c, A, hc, hA, max nL nU, hnL.trans (le_max_left _ _), ?_⟩
    intro U n hn
    refine ⟨hl U n ((le_max_left _ _).trans hn), ?_⟩
    have hun := hu U n ((le_max_right _ _).trans hn)
    rw [paperUpperScale_eq C (hnL.trans ((le_max_left _ _).trans hn)), ← mul_assoc] at hun
    exact hun
  h_mainBracketClaim_of_separate_bounds
theorem paper_exponent_limit  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n => -Real.log (minimaxRMS C n).toReal / Real.log n)
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  have h_paper_exponent_limit_of_mainBracketClaim (hmain : MainBracketClaim C) : Tendsto (fun n => -Real.log (minimaxRMS C n).toReal / Real.log n)
      atTop (𝓝 (rateExponent C.smoothness d)) := exponent_limit_nat_of_rateBracket (hasNatRateBracket_of_mainBracketClaim C hreg hmain)
  (h_paper_exponent_limit_of_mainBracketClaim (paper_main C))
theorem paper_polynomial_bounds  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ c A, 0 < c ∧ 0 < A ∧ ∀ epsilon, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*n^(-rateExponent C.smoothness d-epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A*n^(-rateExponent C.smoothness d) :=
  have h_paper_stretchConstant_pos : 0 < stretchConstant C.smoothness d (paperTau C) := stretchConstant_pos hreg.1 hreg.2 (paperTau_pos C)
  polynomial_bounds_nat_of_rateBracket h_paper_stretchConstant_pos
    (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))
end NearlyMinimax
