module

public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.PairGridChoice

@[expose] public section

/-! Actual Borel pair-difference estimators for the original model.
The low-smoothness branch of Proposition elementary-upper is proved from
the actual sampling measure, rather than an assumed risk envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {d : ℕ} (C : ModelConstants d) (n : ℕ) {k : ℕ} (hk : 0 < k)

def elementaryDenominatorKernel :
    Observation d × Observation d → ℝ := sameLabelKernel (regularObservationLabel hk)

def elementaryNumeratorKernel :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel hk) Prod.snd 0

def elementaryNumerator :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryNumeratorKernel hk)

def elementaryDenominator :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryDenominatorKernel hk)

def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * k ^ d)

def elementaryGridEstimator :
    Estimator d n :=
  ⟨stabilizedRatio C.varianceLower C.varianceUpper (elementaryFloor d k)
      (elementaryNumerator n hk) (elementaryDenominator n hk),
    stabilizedRatio_measurable _ _ _
      (PairUStatistic.pairAverage_measurable n
        (pairWindowScore_measurable _ (regularObservationLabel_measurable hk) measurable_snd 0))
      (PairUStatistic.pairAverage_measurable n
        (sameLabelKernel_measurable _ (regularObservationLabel_measurable hk)))⟩

theorem pairAverage_sub_mul {E : Type*} [MeasurableSpace E] (n : ℕ)
    (K L : E × E → ℝ) (c : ℝ) (x : Fin n → E) :
    PairUStatistic.pairAverage n (fun z => K z - c * L z) x =
      PairUStatistic.pairAverage n K x - c * PairUStatistic.pairAverage n L x := by
  unfold PairUStatistic.pairAverage
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem elementary_score_identity (θ : RegressionParameter d)
    (n k : ℕ) (hk : 0 < k) (z : Fin n → Observation d) :
    elementaryNumerator n hk z - θ.variance * elementaryDenominator n hk z =
      PairUStatistic.pairAverage n (regularPairScore θ hk) z := by
  have he : regularPairScore θ hk =
      (fun z => elementaryNumeratorKernel hk z - θ.variance *
        elementaryDenominatorKernel hk z) := by
    funext z
    unfold regularPairScore elementaryNumeratorKernel elementaryDenominatorKernel
      pairWindowScore sameLabelKernel
    split_ifs <;> ring
  rw [he, pairAverage_sub_mul]
  rfl

theorem elementary_denominator_fluctuation_le {n : ℕ} {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) (hn : 2 ≤ n)
    {k : ℕ} (hk : 0 < k) :
    (∫ z, (elementaryDenominator n hk z - regularGridCollisionMass θ hk) ^ 2
      ∂sampleLaw θ n) ≤
      4 / n * (C.densityUpper / k ^ d) ^ 2 +
      2 / (n * (n - 1 : ℕ)) * (C.densityUpper / k ^ d) := by
  let := observationLaw_isProbability C θ hθ
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ) (fun _ => aemeasurable_id)
  have he := PairUStatistic.pairAverage_centered_sq_le hn hi (fun i => measurePreserving_eval (fun _  => observationLaw θ) i)
    (sameLabelKernel_measurable _ (regularObservationLabel_measurable hk))
    (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable hk))
    (fun x y => (sameLabelKernel_symmetric _
      (regularObservationLabel_measurable hk) (x, y)).symm)
  rw [sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable hk)] at he
  simp [PairUStatistic.rowIntegral] at he
  rw [sameLabelKernel_row_square_integral (observationLaw θ) _
      (regularObservationLabel_measurable hk),
    sameLabelKernel_square_integral (observationLaw θ) _
      (regularObservationLabel_measurable hk)] at he
  simp [regularObservationLabel_mass hθ hk] at he
  exact he.trans (add_le_add
    (mul_le_mul_of_nonneg_left (by apply finite_probability_third_moment_le (regularGridProbability_nonneg θ hk) (regularGridProbability_sum hθ hk) (regularGridProbability_cap hθ hk); exact div_nonneg (by linarith [C.one_lt_densityUpper]) (by positivity)) (by positivity))
    (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper hθ hk) (by positivity)))

def elementaryRowBound : ℝ :=
  responseFourthBound C + (C.varianceUpper + responseSecondBound C) ^ 2

def elementaryKernelBound : ℝ :=
  8 * responseFourthBound C + 2 * C.varianceUpper ^ 2

theorem elementaryRowBound_pos :
    0 < elementaryRowBound C := add_pos_of_pos_of_nonneg (responseFourthBound_pos C) (sq_nonneg _)

theorem elementaryKernelBound_pos :
    0 < elementaryKernelBound C := by
  unfold elementaryKernelBound
  have hh := responseFourthBound_pos C
  positivity

end

section
variable {d n : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (hn : 2 ≤ n)
    {k : ℕ} (hk : 0 < k)

include hθ hn in
theorem elementary_score_fluctuation_le :
    (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ hk) z -
      ∫ p, regularPairScore θ hk p ∂(observationLaw θ).prod (observationLaw θ)) ^ 2
      ∂sampleLaw θ n) ≤
      8 / n * (C.densityUpper / k ^ d) ^ 2 * elementaryRowBound C +
      2 / (n * (n - 1 : ℕ)) * elementaryKernelBound C *
        (C.densityUpper / k ^ d) := by
  let := observationLaw_isProbability C θ hθ
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ) (fun _ => aemeasurable_id)
  have he := PairUStatistic.pairAverage_centered_sq_le hn hi (fun i => measurePreserving_eval (fun _  => observationLaw θ) i)
    (pairWindowScore_measurable _ (regularObservationLabel_measurable hk) measurable_snd θ.variance) (regularPairScore_memLp hθ hk)
    (by unfold pairWindowScore; grind)
  have hV0  := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVU  := hθ.2.2.2.2.2.2.1
  have hC4  := (responseFourthBound_pos C).le
  have hC2  := (responseSecondBound_pos C).le
  have hr : (∫ x, (∫ y, regularPairScore θ hk (x, y) ∂observationLaw θ) ^ 2
      ∂observationLaw θ) ≤
      2 * (C.densityUpper / k ^ d) ^ 2 * elementaryRowBound C := by
    apply (regularPairScore_row_energy_le hθ hk).trans
    unfold elementaryRowBound
    rw [abs_of_nonneg hV0]
    gcongr
  have hq := regularGridCollisionMass_upper hθ hk
  have hq0 : 0 ≤ regularGridCollisionMass θ hk := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hker : (∫ z, regularPairScore θ hk z ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      elementaryKernelBound C * (C.densityUpper / k ^ d) := by
    apply (regularPairScore_kernel_energy_le hθ hk).trans
    unfold elementaryKernelBound
    gcongr
  have hb := he.trans (add_le_add
    (mul_le_mul_of_nonneg_left hr (by positivity))
    (mul_le_mul_of_nonneg_left hker (by positivity)))
  convert hb using 1 <;> first | rfl | ring

include hθ hn in
theorem elementary_score_second_moment_le :
    (∫ z, (elementaryNumerator n hk z - θ.variance * elementaryDenominator n hk z) ^ 2
      ∂sampleLaw θ n) ≤
      8 / n * (C.densityUpper / k ^ d) ^ 2 * elementaryRowBound C +
      2 / (n * (n - 1 : ℕ)) * elementaryKernelBound C *
        (C.densityUpper / k ^ d) +
      ((regularGridOscillation C k ^ 2 / 2) * (C.densityUpper / k ^ d)) ^ 2 := by
  let := observationLaw_isProbability C θ hθ
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have hS := PairUStatistic.pairAverage_memLp_two hi hp (regularPairScore_memLp hθ hk)
  have hmean := PairUStatistic.pairAverage_integral hn hi hp
    (pairWindowScore_measurable _ (regularObservationLabel_measurable hk) measurable_snd θ.variance) (regularPairScore_memLp hθ hk)
  let b := ∫ p, regularPairScore θ hk p ∂(observationLaw θ).prod (observationLaw θ)
  change _ = b at hmean
  have hEq : (∫ z, PairUStatistic.pairAverage n (regularPairScore θ hk) z ^ 2
      ∂sampleLaw θ n) =
      (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ hk) z - b) ^ 2
        ∂sampleLaw θ n) + b ^ 2 := by
    have hv := variance_eq_sub hS
    have hc := variance_eq_integral hS.aemeasurable
    change _ = _ at hv
    simp_all [regularPairScore, sampleLaw]
  have hbm  :=
    (regularPairScore_mean_le hθ hk).trans
      (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper hθ hk)
        (by positivity))
  have hbsq := pow_le_pow_left₀ (regularPairScore_mean_nonneg hθ hk) hbm 2
  simp_rw [elementary_score_identity θ n k hk]
  linarith [elementary_score_fluctuation_le hθ hn hk]

include hθ hn in
theorem elementary_grid_mse_explicit :
    (∫ z, ((elementaryGridEstimator C n hk).val z - θ.variance) ^ 2
      ∂sampleLaw θ n) ≤
      (64 * C.densityUpper ^ 2 * elementaryRowBound C +
        32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) / n +
      (16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)) *
        k ^ d / (n * (n - 1 : ℕ)) +
      2 * C.densityUpper ^ 2 * regularGridOscillation C k ^ 4 := by
  let := observationLaw_isProbability C θ hθ
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have hmN : Measurable (elementaryNumerator (d := d) n hk) :=
    PairUStatistic.pairAverage_measurable n
      (pairWindowScore_measurable _ (regularObservationLabel_measurable hk) measurable_snd 0)
  have hmD : Measurable (elementaryDenominator (d := d) n hk) :=
    PairUStatistic.pairAverage_measurable n
      (sameLabelKernel_measurable _ (regularObservationLabel_measurable hk))
  have hD2  :=
    PairUStatistic.pairAverage_memLp_two hi hp
      (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable hk))
  have hk0 : 0 < k := by exact_mod_cast hk
  have hn0 : 0 < n := by positivity
  have hn1 : 0 < n - 1 := by bound
  have ha : 0 < elementaryFloor d k := by unfold elementaryFloor; positivity
  have hV0  := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hM := stabilized_ratio_mse_le hmN hmD (by
    simp_rw [elementary_score_identity θ n k hk]
    exact PairUStatistic.pairAverage_memLp_two hi hp (regularPairScore_memLp hθ hk)) hD2
    ha hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1 hV0 (by
      convert regularGridCollisionMass_lower hθ hk using 1
      unfold elementaryFloor
      field_simp)
  have hb := hM.trans (mul_le_mul_of_nonneg_left
    (add_le_add (elementary_score_second_moment_le hθ hn hk) (mul_le_mul_of_nonneg_left (elementary_denominator_fluctuation_le hθ hn hk) (sq_nonneg _)))
    (by positivity))
  change (∫ z, ((elementaryGridEstimator C n hk).val z - θ.variance) ^ 2
    ∂sampleLaw θ n) ≤ _ at hb
  convert hb using 1
  unfold elementaryFloor
  field_simp [  hn1.ne']
  <;> ring

def elementaryBiasFactor (C : ModelConstants d) : ℝ :=
  (2 * (d + 1) * C.holderBound) ^ 4 * (Real.sqrt d) ^ (4 * elementarySmoothness C)

theorem regularGridOscillation_fourth (C : ModelConstants d)
    {k : ℕ} (hk : 0 < k) :
    regularGridOscillation C k ^ 4 = elementaryBiasFactor C *
      k ^ (-4 * elementarySmoothness C) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have he : ((Real.sqrt d * (1 / k)) ^ elementarySmoothness C) ^ 4 =
      (Real.sqrt d) ^ (4 * elementarySmoothness C) *
        k ^ (-4 * elementarySmoothness C) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), mul_pow,
      ← Real.rpow_mul_natCast (Real.sqrt_nonneg _),
      ← Real.rpow_mul_natCast (by positivity),
      one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
    congr 2 <;> ring
  grind [regularGridOscillation, elementaryBiasFactor]

def elementaryUpperConstant (C : ModelConstants d) : ℝ :=
  (64 * C.densityUpper ^ 2 * elementaryRowBound C +
    32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) +
    (16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)) +
    (2 * C.densityUpper ^ 2 * elementaryBiasFactor C)

theorem elementaryUpperConstant_pos (C : ModelConstants d) :
    0 < elementaryUpperConstant C := by
  have hU  := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  have hR := elementaryRowBound_pos C
  have hK := elementaryKernelBound_pos C
  simp [elementaryBiasFactor, elementaryUpperConstant] <;> positivity

include hθ hn in
theorem elementary_grid_mse_le :
    (∫ z, ((elementaryGridEstimator C n hk).val z - θ.variance) ^ 2
      ∂sampleLaw θ n) ≤ elementaryUpperConstant C *
      (1 / n + k ^ d / (n * (n - 1 : ℕ)) +
        k ^ (-4 * elementarySmoothness C)) := by
  have hb := elementary_grid_mse_explicit hθ hn hk
  rw [regularGridOscillation_fourth C hk] at hb
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hU  := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  have hR := (elementaryRowBound_pos C).le
  have hK := (elementaryKernelBound_pos C).le
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  apply hb.trans
  let A := 64 * C.densityUpper ^ 2 * elementaryRowBound C +
    32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2
  let B := 16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)
  let E := 2 * C.densityUpper ^ 2 * elementaryBiasFactor C
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hE0 : 0 ≤ E := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + B + E by linarith)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (show B ≤ A + B + E by linarith)
    (show 0 ≤ k ^ d / ((n : ℝ) * (n - 1 : ℕ)) by positivity)
  have h3 := mul_le_mul_of_nonneg_right (show E ≤ A + B + E by linarith)
    (Real.rpow_pos_of_pos hk0 (-4 * elementarySmoothness C)).le
  unfold elementaryUpperConstant
  grind

include hθ hn in
theorem elementary_grid_risk_le :
    meanSquaredRisk (elementaryGridEstimator C n hk) θ ≤
      ENNReal.ofReal (elementaryUpperConstant C *
      (1 / n + k ^ d / (n * (n - 1 : ℕ)) +
        k ^ (-4 * elementarySmoothness C))) := by
  let := sampleLaw_isProbability C θ hθ n
  have hT := (stabilizedRatio_error_memLp (sampleLaw θ n)
    (a := elementaryFloor d k) (PairUStatistic.pairAverage_measurable n (pairWindowScore_measurable _ (regularObservationLabel_measurable hk) measurable_snd 0)) (PairUStatistic.pairAverage_measurable n (sameLabelKernel_measurable _ (regularObservationLabel_measurable hk))) hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1).integrable_sq
  change Integrable (fun z => ((elementaryGridEstimator C n hk).val z - θ.variance) ^ 2)
    _ at hT
  rw [meanSquaredRisk, ← ofReal_integral_eq_lintegral_ofReal hT
    (Eventually.of_forall (fun z => sq_nonneg _))]
  bound [elementary_grid_mse_le hθ hn hk]

end

variable {d n : ℕ} (C : ModelConstants d)

theorem elementary_grid_worstCaseRisk_le
    (hn : 2 ≤ n) {k : ℕ} (hk : 0 < k) :
    worstCaseRisk C (elementaryGridEstimator C n hk) ≤
      ENNReal.ofReal (elementaryUpperConstant C *
      (1 / n + k ^ d / (n * (n - 1 : ℕ)) +
        k ^ (-4 * elementarySmoothness C))) := by
  apply iSup_le
  intro θ
  exact elementary_grid_risk_le θ.property hn hk

def elementaryChosenGrid (n : ℕ) : ℕ :=
  lowSmoothnessGrid d (elementarySmoothness C) n

theorem elementaryChosenGrid_pos (hn : 0 < n) :
    0 < elementaryChosenGrid C n := by
  have hh := lowSmoothnessGrid_ge_four (d := d) (elementarySmoothness_pos C)
    (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  positivity

def elementaryEstimator (n : ℕ) : Estimator d n :=
  if hn : 2 ≤ n then
    elementaryGridEstimator C n (k := (elementaryChosenGrid C n))
      (elementaryChosenGrid_pos C (by omega))
  else constantEstimator d n C.varianceLower

def elementaryRMSConstant : ℝ :=
  2 * Real.sqrt (elementaryUpperConstant C * (2 * 5 ^ d + 1)) +
    (C.varianceUpper - C.varianceLower)

theorem elementary_rms_upper_of_two_le (hn : 2 ≤ n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (elementaryUpperConstant C * (2 * 5 ^ d + 1)) *
        (n ^ (-(1 / 2 : ℝ)) +
          n ^ (-4 * elementarySmoothness C / (d + 4 * elementarySmoothness C)))) := by
  have hn0 : 0 < n := by omega
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hC := (elementaryUpperConstant_pos C).le
  let M := elementaryUpperConstant C *
    pairGridMSEEnvelope d (elementarySmoothness C) n
  have hM0 : 0 ≤ M := by
    dsimp [M, pairGridMSEEnvelope]
    bound
  have he : worstCaseRisk C (elementaryEstimator C n) ≤ ENNReal.ofReal M := by
    unfold elementaryEstimator
    rw [dif_pos hn]
    have hh := elementary_grid_worstCaseRisk_le C hn
      (elementaryChosenGrid_pos C hn0)
    convert hh using 1
    dsimp [M, pairGridMSEEnvelope, elementaryChosenGrid]
    simp_all
  have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num), ← Real.sqrt_eq_rpow] at hh
  exact hh.trans (ENNReal.ofReal_mono (by
    apply pairGrid_rms_of_mse_bound (elementarySmoothness_pos C) hnR hC (Real.sqrt_nonneg M)
    exact le_of_eq (Real.sq_sqrt hM0)))

/-- All sample sizes, including the one-observation constant estimator.
This gives the full low-smoothness branch of the paper's elementary upper. -/
theorem elementary_rms_upper (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max
        ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        (n ^ (-4 * elementarySmoothness C / (d + 4 * elementarySmoothness C)))) := by
  by_cases hn2 : 2 ≤ n
  · apply (elementary_rms_upper_of_two_le C hn2).trans
    apply ENNReal.ofReal_mono
    have hA : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hs : 0 ≤ Real.sqrt (elementaryUpperConstant C * (2 * 5 ^ d + 1)) :=
      Real.sqrt_nonneg _
    have hdiam  := sub_nonneg.mpr C.variance_interval.le
    have hmax := le_max_left ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      (n ^ (-4 * elementarySmoothness C / (d + 4 * elementarySmoothness C)))
    have hmax' := le_max_right ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      (n ^ (-4 * elementarySmoothness C / (d + 4 * elementarySmoothness C)))
    unfold elementaryRMSConstant
    nlinarith [mul_nonneg hdiam (hA.trans hmax)]
  · have hn1 : n = 1 := by omega
    subst n
    have he : worstCaseRisk C (constantEstimator d 1 C.varianceLower) ≤
        ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) := by
      apply iSup_le
      intro θ
      exact constantEstimator_risk_bound C θ.val θ.property
    have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (sub_nonneg.mpr C.variance_interval.le)] at hh
    apply hh.trans
    apply ENNReal.ofReal_mono
    simp [elementaryRMSConstant]

theorem elementary_upper_low_smoothness {C : ModelConstants d}
    (hs : C.smoothness ≤ 1) (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        (n ^ (-4 * C.smoothness / (d + 4 * C.smoothness)))) := by
  simpa only [elementarySmoothness, min_eq_left hs] using elementary_rms_upper C hn

end NearlyMinimax
