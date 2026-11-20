module

public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.PairGridChoice
public import NearlyMinimax.PairLocalization

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

def elementaryDenominatorKernel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    ObservationPair d → ℝ := sameLabelKernel (regularObservationLabel k hk)

def elementaryNumeratorKernel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    ObservationPair d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd 0

def elementaryNumerator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    ObservedSample d n → ℝ :=
  PairUStatistic.pairAverage n (elementaryNumeratorKernel k hk)

def elementaryDenominator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    ObservedSample d n → ℝ :=
  PairUStatistic.pairAverage n (elementaryDenominatorKernel k hk)

def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * (k : ℝ) ^ d)

section
variable {d : ℕ} (n k : ℕ) (hk : 0 < k)

theorem elementaryNumerator_measurable :
    Measurable (elementaryNumerator (d := d) n k hk) :=
  PairUStatistic.pairAverage_measurable n
    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk) Prod.snd measurable_snd 0)

theorem elementaryDenominator_measurable :
    Measurable (elementaryDenominator (d := d) n k hk) :=
  PairUStatistic.pairAverage_measurable n
    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))

end

def elementaryGridEstimator {d : ℕ} (C : ModelConstants d) (n k : ℕ) (hk : 0 < k) :
    Estimator d n :=
  ⟨stabilizedRatio C.varianceLower C.varianceUpper (elementaryFloor d k)
      (elementaryNumerator n k hk) (elementaryDenominator n k hk),
    stabilizedRatio_measurable _ _ _ (elementaryNumerator_measurable n k hk)
      (elementaryDenominator_measurable n k hk)⟩

theorem pairAverage_sub_mul {E : Type*} [MeasurableSpace E] (n : ℕ)
    (K L : E × E → ℝ) (c : ℝ) (x : Fin n → E) :
    PairUStatistic.pairAverage n (fun z => K z - c * L z) x =
      PairUStatistic.pairAverage n K x - c * PairUStatistic.pairAverage n L x := by
  unfold PairUStatistic.pairAverage
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem elementary_score_identity {d : ℕ} (θ : RegressionParameter d)
    (n k : ℕ) (hk : 0 < k) (z : ObservedSample d n) :
    elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z =
      PairUStatistic.pairAverage n (regularPairScore θ k hk) z := by
  have he : regularPairScore θ k hk =
      (fun z => elementaryNumeratorKernel k hk z - θ.variance *
        elementaryDenominatorKernel k hk z) := by
    funext z
    unfold regularPairScore elementaryNumeratorKernel elementaryDenominatorKernel
      pairWindowScore sameLabelKernel
    split_ifs <;> ring
  rw [he, pairAverage_sub_mul]
  rfl

/-- The two kernels use the same partition. Their row energies cost at most
one cell's mass times the full kernel energy. -/
private theorem sample_pair_energy {d n k : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n) (hk : 0 < k)
    {K : ObservationPair d → ℝ} (hm : Measurable K) (hK : MemLp K 2 (observationPairLaw θ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    (hsupp : ∀ x y, regularObservationLabel k hk x ≠ regularObservationLabel k hk y → K (x, y) = 0) :
    MemLp (PairUStatistic.pairAverage n K) 2 (sampleLaw θ n) ∧
    (∫ z, PairUStatistic.pairAverage n K z ∂sampleLaw θ n) = (∫ z, K z ∂observationPairLaw θ) ∧
    (∫ z, (PairUStatistic.pairAverage n K z - ∫ y, K y ∂observationPairLaw θ) ^ 2 ∂sampleLaw θ n) ≤
      (4 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) + 2 / ((n : ℝ) * (n - 1 : ℕ))) *
        ∫ z, K z ^ 2 ∂observationPairLaw θ := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  let X (i : Fin n) (z : ObservedSample d n) := z i
  exact ⟨PairUStatistic.pairAverage_memLp_two X hi hp hK,
    PairUStatistic.pairAverage_integral hn X hi hp hm hK,
    PairUStatistic.partition_pairAverage_centered_sq_le hn X hi hp
      (regularObservationLabel k hk) (regularObservationLabel_measurable k hk) hm hK hsym hsupp
      (fun c => by rw [regularObservationLabel_mass C θ hθ]; exact regularGridProbability_cap C θ hθ k hk c)⟩

def elementaryBiasFactor {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * ((d : ℝ) + 1) * C.holderBound) ^ 4 * (Real.sqrt d) ^ (4 * elementarySmoothness C)

theorem regularGridOscillation_fourth {d : ℕ} (C : ModelConstants d)
    (k : ℕ) (hk : 0 < k) :
    regularGridOscillation C k ^ 4 = elementaryBiasFactor C *
      (k : ℝ) ^ (-4 * elementarySmoothness C) := by
  have hk0 : 0 < (k : ℝ) := by simp_all
  have he : ((Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C) ^ 4 =
      (Real.sqrt d) ^ (4 * elementarySmoothness C) *
        (k : ℝ) ^ (-4 * elementarySmoothness C) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), mul_pow,
      ← Real.rpow_mul_natCast (Real.sqrt_nonneg _),
      ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / (k : ℝ)),
      one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
    ring
  unfold regularGridOscillation elementaryBiasFactor
  rw [mul_pow, he]
  ring

def elementaryTotalEnergy {d : ℕ} (C : ModelConstants d) : ℝ :=
  8 * responseFourthBound C + 3 * C.varianceUpper ^ 2

def elementaryUpperConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (32 * C.densityUpper ^ 2 + 16 * C.densityUpper) * elementaryTotalEnergy C +
    2 * C.densityUpper ^ 2 * elementaryBiasFactor C

theorem elementaryUpperConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementaryUpperConstant C := by
  have := responseFourthBound_pos C
  have : 0 < C.densityUpper := zero_lt_one.trans C.one_lt_densityUpper
  unfold elementaryUpperConstant elementaryTotalEnergy elementaryBiasFactor
  positivity

section
variable {d n : ℕ} (C : ModelConstants d)

theorem elementary_grid_risk_le
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    meanSquaredRisk (elementaryGridEstimator C n k hk) θ ≤
      ENNReal.ofReal (elementaryUpperConstant C *
      (1 / (n : ℝ) + (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
        (k : ℝ) ^ (-4 * elementarySmoothness C))) := by
  classical
  let μ := observationLaw θ
  let ν := sampleLaw θ n
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  let cap := C.densityUpper / (k : ℝ) ^ d
  let L := 4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ))
  let B := 8 * responseFourthBound C + 2 * C.varianceUpper ^ 2
  let m := regularGridCollisionMass θ k hk
  let S := PairUStatistic.pairAverage n (regularPairScore θ k hk)
  let b := ∫ z, regularPairScore θ k hk z ∂observationPairLaw θ
  let label := regularObservationLabel (d := d) k hk
  have hl := regularObservationLabel_measurable (d := d) k hk
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVU := hθ.2.2.2.2.2.2.1
  have hU : 0 < C.densityUpper := zero_lt_one.trans C.one_lt_densityUpper
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hC4 := responseFourthBound_pos C
  have hL : 0 ≤ L := by dsimp [L, cap]; positivity
  have hm : m ≤ cap := regularGridCollisionMass_upper C θ hθ k hk
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨hD, _, hd⟩ := sample_pair_energy C θ hθ hn hk (sameLabelKernel_measurable label hl)
    (sameLabelKernel_memLp μ label hl) (fun x y => (sameLabelKernel_symmetric label hl (x, y)).symm)
    (fun x y h => by simp [sameLabelKernel, label, h])
  rw [sameLabelKernel_integral μ label hl, sameLabelKernel_square_integral μ label hl] at hd
  simp only [μ, label, regularObservationLabel_mass C θ hθ] at hd
  have hd' : (∫ z, (elementaryDenominator n k hk z - m) ^ 2 ∂ν) ≤ L * cap :=
    hd.trans (mul_le_mul_of_nonneg_left hm hL)
  obtain ⟨hS, hb, hs⟩ := sample_pair_energy C θ hθ hn hk (K := regularPairScore θ k hk)
    (pairWindowScore_measurable label hl Prod.snd measurable_snd θ.variance)
    (regularPairScore_memLp C θ hθ k hk) (pairWindowScore_symmetric label Prod.snd θ.variance)
    (fun x y h => by simp [regularPairScore, pairWindowScore, h])
  change MemLp S 2 ν at hS
  change (∫ z, S z ∂ν) = b at hb
  have hE : (∫ z, regularPairScore θ k hk z ^ 2 ∂observationPairLaw θ) ≤ B * cap := by
    apply (regularPairScore_kernel_energy_le C θ hθ k hk).trans
    dsimp [B]
    gcongr
  have hmb := (regularPairScore_mean_le C θ hθ k hk).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))
  have hbs := pow_le_pow_left₀ (regularPairScore_mean_nonneg C θ hθ k hk) hmb 2
  have hS2 : (∫ z, S z ^ 2 ∂ν) ≤ L * (B * cap) + ((regularGridOscillation C k ^ 2 / 2) * cap) ^ 2 := by
    have he := variance_eq_sub hS
    rw [variance_eq_integral hS.aemeasurable, hb] at he
    simp only [Pi.pow_apply] at he
    have hf := hs.trans (mul_le_mul_of_nonneg_left hE hL)
    grind
  have ha : 0 < elementaryFloor d k := by unfold elementaryFloor; positivity
  have hED : 2 * elementaryFloor d k ≤ m := by
    convert regularGridCollisionMass_lower C θ hθ k hk using 1
    unfold elementaryFloor
    ring
  have hScore : MemLp (fun z => elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z)
      2 ν := by
    simpa only [elementary_score_identity] using hS
  apply (stabilized_ratio_lintegral_mse_le ν (elementaryNumerator_measurable n k hk)
    (elementaryDenominator_measurable n k hk) hScore hD ha hθ.2.2.2.2.2.1 hVU hV0 hED).trans
  apply ENNReal.ofReal_mono
  simp only [elementary_score_identity]
  apply (mul_le_mul_of_nonneg_left (add_le_add hS2 (mul_le_mul_of_nonneg_left hd' (sq_nonneg _))) (by positivity)).trans
  have he : 0 ≤ elementaryTotalEnergy C := by unfold elementaryTotalEnergy; positivity
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  calc
    _ = 32 * C.densityUpper ^ 2 * elementaryTotalEnergy C * (1 / (n : ℝ)) +
        16 * C.densityUpper * elementaryTotalEnergy C * ((k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ))) +
        2 * C.densityUpper ^ 2 * elementaryBiasFactor C * (k : ℝ) ^ (-4 * elementarySmoothness C) := by
      dsimp [elementaryFloor, L, cap, B, elementaryTotalEnergy]
      rw [mul_assoc (2 * C.densityUpper ^ 2), ← regularGridOscillation_fourth C k hk]
      field_simp <;> ring
    _ ≤ _ := by
      rw [mul_add, mul_add]
      refine add_le_add (add_le_add (mul_le_mul_of_nonneg_right ?_ (by positivity))
        (mul_le_mul_of_nonneg_right ?_ (by positivity))) (mul_le_mul_of_nonneg_right ?_ (by positivity))
      all_goals unfold elementaryUpperConstant
      all_goals nlinarith only [mul_nonneg (show 0 ≤ 32 * C.densityUpper ^ 2 by positivity) he,
          mul_nonneg (show 0 ≤ 16 * C.densityUpper by positivity) he,
          mul_nonneg (show 0 ≤ 2 * C.densityUpper ^ 2 by positivity) hB]

end

def elementaryChosenGrid {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℕ :=
  lowSmoothnessGrid d (elementarySmoothness C) n

theorem elementaryChosenGrid_pos {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    0 < elementaryChosenGrid C n := by
  have hh := lowSmoothnessGrid_ge_four (d := d) (elementarySmoothness_pos C)
    (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  unfold elementaryChosenGrid
  omega

def elementaryEstimator {d : ℕ} (C : ModelConstants d) (n : ℕ) : Estimator d n :=
  if hn : 2 ≤ n then
    elementaryGridEstimator C n (elementaryChosenGrid C n)
      (elementaryChosenGrid_pos C (by omega))
  else constantEstimator d n C.varianceLower

def elementaryRMSConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  2 * Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) +
    (C.varianceUpper - C.varianceLower)

section
variable {d n : ℕ} (C : ModelConstants d)

theorem elementary_rms_upper_of_two_le (hn : 2 ≤ n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
          (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
  have hn0 : 0 < n := by omega
  have hnR : 2 ≤ (n : ℝ) := by simp_all
  have hC := (elementaryUpperConstant_pos C).le
  let M := elementaryUpperConstant C *
    pairGridMSEEnvelope d (elementarySmoothness C) n
  have hM0 : 0 ≤ M := by
    dsimp [M, pairGridMSEEnvelope]
    have hnp : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have he : worstCaseRisk C (elementaryEstimator C n) ≤ ENNReal.ofReal M := by
    unfold elementaryEstimator
    rw [dif_pos hn]
    apply iSup_le
    intro θ
    simpa [M, pairGridMSEEnvelope, elementaryChosenGrid, Nat.cast_sub (by omega : 1 ≤ n)] using
      elementary_grid_risk_le C θ.val θ.property hn (elementaryChosenGrid C n) (elementaryChosenGrid_pos C hn0)
  have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num), ← Real.sqrt_eq_rpow] at hh
  have hs : Real.sqrt M ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
        (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C))) := by
    apply pairGrid_rms_of_mse_bound (elementarySmoothness_pos C) hnR hC (Real.sqrt_nonneg M)
    exact le_of_eq (Real.sq_sqrt hM0)
  exact hh.trans (ENNReal.ofReal_mono hs)

/-- All sample sizes, including the one-observation constant estimator.
This gives the full low-smoothness branch of the paper's elementary upper. -/
theorem elementary_rms_upper (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max
        ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
  by_cases hn2 : 2 ≤ n
  · apply (elementary_rms_upper_of_two_le C hn2).trans
    apply ENNReal.ofReal_mono
    have hA : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hs : 0 ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) :=
      Real.sqrt_nonneg _
    have hdiam := sub_nonneg.mpr C.variance_interval.le
    have hmax := le_max_left ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
    have hmax' := le_max_right ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
    have hm0 := hA.trans hmax
    unfold elementaryRMSConstant
    nlinarith [mul_nonneg hdiam hm0]
  · have hn1 : n = 1 := by omega
    subst n
    unfold elementaryEstimator
    rw [dif_neg (by decide : ¬2 ≤ (1 : ℕ))]
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
    simp only [Nat.cast_one, Real.one_rpow, max_self, mul_one]
    unfold elementaryRMSConstant
    norm_num

theorem elementary_upper_low_smoothness
    (hs : C.smoothness ≤ 1) (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))) := by
  simpa only [elementarySmoothness, min_eq_left hs] using elementary_rms_upper C hn

end

end NearlyMinimax
