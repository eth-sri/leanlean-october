module

public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.PairGridChoice
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual Borel pair-difference estimators for the original model.
The low-smoothness branch of Proposition elementary-upper is proved from
the actual sampling measure, rather than an assumed risk envelope. -/
𝛏
𝚨

𝗇 𝔟 𝖰
𝗇 𝕵 𝗰 → ℝ
𝗃 𝖇 ἀ k hk
𝗇 𝕶 𝖇 regularObservationLabel
def elementaryDenominatorKernel (k : ℕ) (hk : 𝔟) :
    𝕵 := sameLabelKernel 𝕶

def elementaryNumeratorKernel (k : ℕ) (hk : 𝔟) :
    𝕵 :=
  pairWindowScore 𝕶 Prod.snd 0

𝗇 𝔶 𝙌
def elementaryNumerator (n k : ℕ) (hk : 𝔟) :
    𝔶 → ℝ :=
  PairUStatistic.pairAverage n 𝖇 elementaryNumeratorKernel

def elementaryDenominator (n k : ℕ) (hk : 𝔟) :
    𝔶 → ℝ :=
  PairUStatistic.pairAverage n 𝖇 elementaryDenominatorKernel

𝗃 𝖈 (ἀ : ℝ)
𝗇 𝔢 𝖈 k
def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * 𝔢 ^ d)

𝗇 𝔊 𝖇 regularObservationLabel_measurable
𝗇 𝔭 PairUStatistic.pairAverage_measurable n $ pairWindowScore_measurable _ 𝔊 Prod.snd measurable_snd 0
𝗇 𝖀 sameLabelKernel_measurable _ 𝔊
𝗇 𝔰 PairUStatistic.pairAverage_measurable n 𝖀
𝗇 𝕷 elementaryFloor d k
𝗇 𝕽 elementaryDenominator n k hk
def elementaryGridEstimator (C : ModelConstants d) (n k : ℕ) (hk : 𝔟) :
    𝚠 :=
  ⟨stabilizedRatio C.varianceLower C.varianceUpper 𝕷
      (elementaryNumerator n k hk) 𝕽,
    stabilizedRatio_measurable _ _ _
      𝔭
      𝔰⟩

theorem pairAverage_sub_mul [MeasurableSpace E] n
    K L c (x : 𝗚₁) :
    PairUStatistic.pairAverage n (fun z => K z - c * L z) x =
      PairUStatistic.pairAverage n K x - c * PairUStatistic.pairAverage n L x := by
  unfold PairUStatistic.pairAverage
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

𝗇 𝔵 regularPairScore θ k hk
𝗇 𝔉 PairUStatistic.pairAverage n 𝔵 z
𝗇 𝔔 elementaryNumerator n k hk z - θ.variance * 𝕽 z
theorem elementary_score_identity (θ : RegressionParameter d)
    n k hk z :
    𝔔 =
      𝔉 := by
  have he : 𝔵 =
       fun z => 𝖇 elementaryNumeratorKernel z - θ.variance *
        𝖇 elementaryDenominatorKernel z := by
    funext z
    unfold regularPairScore elementaryNumeratorKernel elementaryDenominatorKernel
      pairWindowScore sameLabelKernel
    bound
  rw [he, pairAverage_sub_mul]
  rfl

𝗇 𝔄 fun i (z : 𝔶) => z i
𝗇 𝔍 fun _ : Fin n => observationLaw θ
𝗇 𝔎 C.densityUpper / 𝗋
𝗇 𝔏 𝗷
𝗇 𝖁 (𝗈 : ℕ)
𝗇 𝔒 𝖁
𝗇 𝔘 𝗏
𝗇 𝔙 fun _ => aemeasurable_id
𝗇 𝔛 sampleLaw_isProbability C θ hθ n
𝗃 𝕮 ἀ C θ hθ k hk
𝗇 𝔣 𝕮 regularGridCollisionMass_upper
𝗇 𝔨 𝙟
𝗇 𝔪 𝙱
𝗇 𝔮 iIndepFun_pi (μ := 𝔍) 𝔙
𝗃 𝖄 ἀ (observationLaw θ) _ 𝔊
𝗇 𝔳 𝖄 sameLabelKernel_memLp
𝗇 𝕴 PairUStatistic.pairAverage_centered_sq_le hn 𝔄 hi $ measurePreserving_eval 𝔍
𝗇 𝕸 𝘬₁
𝗇 𝖂 2 / (n * 𝔒)
𝗃 𝖅 ἀ ^ 2
theorem elementary_denominator_fluctuation_le C
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    k hk :
     ∫ z, (𝕽 z - 𝕸) ^ 2
      ∂ 𝔏 ≤
      4 / n * 𝖅 𝔎 +
      𝖂 * 𝔎 := by
  let := 𝔪
  let := 𝔛
  have hi := 𝔮
  have he := 𝕴
    𝖀
    𝔳
     fun x y => (sameLabelKernel_symmetric _
      𝔊 𝖮).symm
  rw [𝖄 sameLabelKernel_integral] at he
  simp only [PairUStatistic.rowIntegral] at he
  rw [𝖄 sameLabelKernel_row_square_integral,
    𝖄 sameLabelKernel_square_integral] at he
  simp only [𝕮 regularObservationLabel_mass] at he
  have hm := 𝔣
  exact he.trans $ add_le_add
    (mul_le_mul_of_nonneg_left 𝕮 regularGridCollisionRowEnergy_upper $ by positivity )
    $ mul_le_mul_of_nonneg_left hm $ by positivity

def elementaryRowBound (C : ModelConstants d) : ℝ :=
  responseFourthBound C + (C.varianceUpper + responseSecondBound C) ^ 2

def elementaryKernelBound (C : ModelConstants d) : ℝ :=
  8 * responseFourthBound C + 2 * 𝖅 C.varianceUpper

section

𝛇

theorem elementaryRowBound_pos :
    0 < elementaryRowBound C := add_pos_of_pos_of_nonneg (responseFourthBound_pos C) $ sq_nonneg _

theorem elementaryKernelBound_pos :
    0 < elementaryKernelBound C := by
  unfold elementaryKernelBound
  have hh := responseFourthBound_pos C
  positivity

end

𝗇 𝔗 𝕮 regularPairScore_memLp
𝗇 𝕾 𝖶
𝗇 𝔚 ∫ p, 𝔵 p ∂𝕾
𝗇 𝔬 8 / n * 𝖅 𝔎 * elementaryRowBound C + 𝖂 * elementaryKernelBound C * 𝔎
𝗇 𝔴 pairWindowScore_measurable _ 𝔊 Prod.snd measurable_snd θ.variance
𝗃 𝕯 ∫ z, (𝔉 - ἀ) ^ 2 ∂ 𝔏
𝗃 𝖆 (ἀ C).le
theorem elementary_score_fluctuation_le C
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    k hk :
    𝕯 𝔚 ≤
      𝔬 := by
  let := 𝔪
  let := 𝔛
  have hi := 𝔮
  have he := 𝕴
    𝔴 𝔗
    $ pairWindowScore_symmetric _ Prod.snd θ.variance
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVU := hθ.2.2.2.2.2.2.1
  have hC4 := 𝖆 responseFourthBound_pos
  have hC2 := 𝖆 responseSecondBound_pos
  have hr : ∫ x, (∫ y, 𝔵 𝖮 ∂observationLaw θ) ^ 2
      ∂observationLaw θ ≤
      2 * 𝖅 𝔎 * elementaryRowBound C := by
    apply (𝕮 regularPairScore_row_energy_le).trans
    unfold elementaryRowBound
    rw [abs_of_nonneg hV0]
    gcongr
  have hq := 𝔣
  have hq0 : 0 ≤ 𝕸 := by
    unfold regularGridCollisionMass
    positivity
  have hker : ∫ z, 𝔵 z ^ 2
      ∂𝕾 ≤
      elementaryKernelBound C * 𝔎 := by
    apply (𝕮 regularPairScore_kernel_energy_le).trans
    unfold elementaryKernelBound
    bound
  have hb := he.trans $ add_le_add
    (mul_le_mul_of_nonneg_left hr $ by positivity )
    $ mul_le_mul_of_nonneg_left hker $ by positivity
  convert hb using 1 <;> first | rfl | ring

𝗇 𝔡 PairUStatistic.pairAverage n 𝔵
𝗇 𝔱 ∫ z, 𝔉 ∂ 𝔏
𝗃 𝖊 ∫ z, 𝖅 ἀ ∂ 𝔏
𝗇 𝔲 𝖊 𝔉
𝗃 𝕰 ἀ C θ hθ hn k hk
𝗇 𝕹 PairUStatistic.pairAverage_memLp_two 𝔄 hi hp
theorem elementary_score_second_moment_le C
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    k hk :
    𝖊 𝔔 ≤
      𝔬 +
      ( regularGridOscillation C k ^ 2 / 2 * 𝔎) ^ 2 := by
  let := 𝔪
  let := 𝔛
  have hi := 𝔮
  have hp := measurePreserving_eval 𝔍
  have hS := 𝕹 𝔗
  have hmean := PairUStatistic.pairAverage_integral hn
    𝔄 hi hp
    𝔴 𝔗
  let b := 𝔚
  change 𝔱 = b at hmean
  have hEq : 𝔲 =
      𝕯 b + 𝖅 b := by
    have hv := variance_eq_sub hS
    have hc := variance_eq_integral hS.aemeasurable
    change variance 𝔡
      𝔏 = 𝔲 - 𝖅 𝔱 at hv
    change variance 𝔡
      𝔏 = 𝕯 𝔱 at hc
    simp_all
  have hbm :=
    (𝕮 regularPairScore_mean_le).trans
      $ mul_le_mul_of_nonneg_left 𝔣
        $ by positivity
  have hbsq := pow_le_pow_left₀ 𝕮 regularPairScore_mean_nonneg hbm 2
  simp_rw [elementary_score_identity θ n k hk]
  rw [hEq]
  exact add_le_add 𝕰 elementary_score_fluctuation_le hbsq

𝗇 𝔷 elementaryGridEstimator C n k hk
𝗇 𝔐 ((𝔷).val z - θ.variance) ^ 2
𝗇 𝖃 𝖅 C.densityUpper
𝗇 𝔑 64 * 𝖃 * elementaryRowBound C + 32 * 𝖃 * 𝖅 C.varianceUpper
𝗇 𝔖 16 * C.densityUpper * (elementaryKernelBound C + 𝖅 C.varianceUpper)
𝗇 𝔜 𝖈 n
𝗃 𝖉 ἀ (d := d)
𝗇 𝔤 𝖉 elementaryNumerator n k hk
𝗇 𝔥 𝖉 elementaryDenominator n k hk
𝗇 𝔯 ∫ z, 𝔐 ∂ 𝔏
𝗇 𝕱 𝗧₁
𝗇 𝕺 𝔜 * 𝔒
theorem elementary_grid_mse_explicit (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    (k : ℕ) (hk : 𝔟) :
    𝔯 ≤
      𝔑 / 𝔜 +
      𝔖 *
        𝔢 ^ d / 𝕺 +
      2 * 𝖃 * regularGridOscillation C k ^ 4 := by
  let := 𝔪
  let := 𝔛
  have hi := 𝔮
  have hp := measurePreserving_eval 𝔍
  have hmN : Measurable 𝔤 :=
    𝔭
  have hmD : Measurable 𝔥 :=
    𝔰
  have hS2 : MemLp (fun z => 𝔔) 2 𝔏 := by
    simp_rw [elementary_score_identity θ n k hk]
    exact 𝕹 𝔗
  have hD2 :=
    𝕹
      𝔳
  have hk0 : 𝔟 := by exact_mod_cast hk
  have hn0 : 𝕱 := by positivity
  have hn1 : 0 < 𝔒 := by simpa
  have hED : 2 * 𝕷 ≤ 𝕸 := by
    convert 𝕮 regularGridCollisionMass_lower using 1
    unfold elementaryFloor
    field_simp
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hM := stabilized_ratio_mse_le 𝔏 hmN hmD hS2 hD2
    (by unfold elementaryFloor; positivity) hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1 hV0 hED
  have hS := 𝕰 elementary_score_second_moment_le
  have hD := 𝕰 elementary_denominator_fluctuation_le
  have hb := hM.trans $ mul_le_mul_of_nonneg_left
    (add_le_add hS $ mul_le_mul_of_nonneg_left hD $ sq_nonneg _ )
    $ by positivity
  change 𝔯 ≤ _ at hb
  convert hb using 1
  unfold elementaryFloor
  field_simp [hk0.ne', hn0.ne', hn1.ne', pow_ne_zero d hk0.ne']
  <;> ring

𝗇 𝔩 Real.sqrt d ^ (4 * elementarySmoothness C)
def elementaryBiasFactor (C : ModelConstants d) : ℝ :=
  (2 * (𝖈 d + 1) * C.holderBound) ^ 4 * 𝔩

𝗇 𝕭 -4 * elementarySmoothness C
𝗇 𝔠 𝕭
theorem regularGridOscillation_fourth (C : ModelConstants d)
    k (hk : 𝔟) :
    regularGridOscillation C k ^ 4 = elementaryBiasFactor C *
      k ^ 𝔠 := by
  have hk0 : 0 < 𝔢 := by exact_mod_cast hk
  have he : ((Real.sqrt d * 𝚖₂) ^ elementarySmoothness C) ^ 4 =
      𝔩 *
        k ^ 𝔠 := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) $ by positivity , mul_pow,
      ← Real.rpow_mul_natCast $ Real.sqrt_nonneg _ ,
      ← Real.rpow_mul_natCast $ by positivity ,
      one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
    ring
  unfold regularGridOscillation elementaryBiasFactor
  grind

𝗇 𝔫 2 * 𝖃 * elementaryBiasFactor C
def elementaryUpperConstant (C : ModelConstants d) : ℝ :=
  𝔑 +
    𝔖 +
    𝔫

𝗇 𝔦 𝙋
theorem elementaryUpperConstant_pos (C : ModelConstants d) :
    0 < elementaryUpperConstant C := by
  have hU := (by norm_num : 𝔦 < 1).trans C.one_lt_densityUpper
  have hR := elementaryRowBound_pos C
  have hK := elementaryKernelBound_pos C
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  unfold elementaryUpperConstant
  positivity

𝗇 𝔇 elementaryUpperConstant C * (1 / n + 𝗋 / (n * 𝖁) + k ^ 𝕭)
𝗇 𝕲 A + B + E
theorem elementary_grid_mse_le C
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    k hk :
    𝔯 ≤ 𝔇 := by
  have hb := 𝕰 elementary_grid_mse_explicit
  rw [regularGridOscillation_fourth C k hk] at hb
  have hk0 : 0 < 𝔢 := by exact_mod_cast hk
  have hU := (by norm_num : 𝔦 < 1).trans C.one_lt_densityUpper
  have hR := 𝖆 elementaryRowBound_pos
  have hK := 𝖆 elementaryKernelBound_pos
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  let A := 𝔑
  let B := 𝔖
  let E := 𝔫
  have hA0 : 𝖲₁ := by positivity
  have hB0 : 𝙐 := by positivity
  have hE0 : 𝘃₂ := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show A ≤ 𝕲 by linarith)
    $ show 0 ≤ 1 / 𝔜 by positivity
  have h2 := mul_le_mul_of_nonneg_right (show B ≤ 𝕲 by linarith)
    $ show 0 ≤ 𝗋 / 𝕺 by positivity
  have h3 := mul_le_mul_of_nonneg_right (show E ≤ 𝕲 by linarith)
    (Real.rpow_pos_of_pos hk0 𝔠).le
  unfold elementaryUpperConstant
  grind

theorem elementary_grid_risk_le C
    (θ : RegressionParameter d) (hθ : 𝔨) (hn : 𝔘)
    k hk :
    meanSquaredRisk 𝔷 θ ≤
      ENNReal.ofReal 𝔇 := by
  let := 𝔛
  have hmN : Measurable 𝔤 :=
    𝔭
  have hmD : Measurable 𝔥 :=
    𝔰
  have hT := (stabilizedRatio_error_memLp 𝔏
    (a := 𝕷) hmN hmD hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1).integrable_sq
  change Integrable (fun z => 𝔐)
    𝔏 at hT
  rw [meanSquaredRisk, ← ofReal_integral_eq_lintegral_ofReal hT
    $ Eventually.of_forall fun z => sq_nonneg _ ]
  exact ENNReal.ofReal_mono 𝕰 elementary_grid_mse_le

theorem elementary_grid_worstCaseRisk_le (C : ModelConstants d)
    (hn : 𝔘) k hk :
    worstCaseRisk C 𝔷 ≤
      ENNReal.ofReal 𝔇 := by
  apply iSup_le
  intro θ
  exact elementary_grid_risk_le C θ.val θ.property hn k hk

def elementaryChosenGrid (C : ModelConstants d) (n : ℕ) : ℕ :=
  lowSmoothnessGrid d (elementarySmoothness C) n

𝗇 𝕳 elementaryChosenGrid C n
theorem elementaryChosenGrid_pos (C : ModelConstants d) (hn : 𝕱) :
    0 < 𝕳 := by
  have hh := 𝖉 lowSmoothnessGrid_ge_four (elementarySmoothness_pos C)
    $ show 1 ≤ 𝔜 by exact_mod_cast hn
  unfold elementaryChosenGrid
  omega

def elementaryEstimator (C : ModelConstants d) (n : ℕ) : 𝚠 :=
  if hn : 𝔘 then
    elementaryGridEstimator C n 𝕳
      $ elementaryChosenGrid_pos C $ by omega
  else constantEstimator d n C.varianceLower

𝗇 𝕻 C.varianceUpper - C.varianceLower
def elementaryRMSConstant (C : ModelConstants d) : ℝ :=
  2 * Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) +
    𝕻

section

𝛇

𝗇 𝔅 n ^ (𝕭 / (d + 4 * elementarySmoothness C))
𝗇 𝕬 (𝙖 : ℝ)
𝗇 𝕿 worstCaseRisk C $ elementaryEstimator C n
𝗇 𝔓 𝕿 ^ 𝕬
𝗇 𝔞 elementaryUpperConstant C * (2 * 5 ^ d + 1)
𝗇 𝔧 n ^ (-𝕬)
𝗇 𝕼 𝔧 + 𝔅
theorem elementary_rms_upper_of_two_le (hn : 𝔘) :
    𝔓 ≤
      ENNReal.ofReal (Real.sqrt (elementaryUpperConstant C * (2 * 5 ^ d + 1)) *
        𝕼) := by
  have hn0 : 𝕱 := by omega
  have hC := 𝖆 elementaryUpperConstant_pos
  let M := elementaryUpperConstant C *
    pairGridMSEEnvelope d (elementarySmoothness C) n
  have hM0 : 𝙷 := by
    dsimp [M, pairGridMSEEnvelope]
    bound
  have he : 𝕿 ≤ ENNReal.ofReal M := by
    unfold elementaryEstimator
    rw [dif_pos hn]
    have hh := elementary_grid_worstCaseRisk_le C hn 𝕳
      $ elementaryChosenGrid_pos C hn0
    convert hh using 1
    dsimp [M, pairGridMSEEnvelope, elementaryChosenGrid]
    simp_all
  have hh := ENNReal.rpow_le_rpow he (by norm_num : 𝔦 ≤ 𝙖)
  rw [ENNReal.ofReal_rpow_of_nonneg hM0 $ by norm_num , ← Real.sqrt_eq_rpow] at hh
  have hs : Real.sqrt M ≤ Real.sqrt 𝔞 *
      𝕼 := by
    apply pairGrid_rms_of_mse_bound (elementarySmoothness_pos C) (by exact_mod_cast hn) hC $ Real.sqrt_nonneg M
    grind
  exact hh.trans $ ENNReal.ofReal_mono hs

𝗇 𝔈 𝖈 n ^ (-𝕬)
/-- All sample sizes, including the one-observation constant estimator.
This gives the full low-smoothness branch of the paper's elementary upper. -/
theorem elementary_rms_upper (hn : 𝕱) :
    𝔓 ≤
      ENNReal.ofReal (elementaryRMSConstant C * max
        𝔈
        𝔅) := by
  by_cases hn2 : 𝔘
  · apply (elementary_rms_upper_of_two_le C hn2).trans
    apply ENNReal.ofReal_mono
    have hA : 0 ≤ 𝔈 := by positivity
    have hs : 0 ≤ Real.sqrt 𝔞 :=
      Real.sqrt_nonneg _
    have hdiam := sub_nonneg.mpr C.variance_interval.le
    have hmax := le_max_left 𝔈
      𝔅
    have hmax' := le_max_right 𝔈
      𝔅
    unfold elementaryRMSConstant
    nlinarith
  · have hn1 : n = 1 := by omega
    subst n
    have he : worstCaseRisk C (constantEstimator d 1 C.varianceLower) ≤
        ENNReal.ofReal 𝖅 𝕻 := by
      apply iSup_le
      intro θ
      exact constantEstimator_risk_bound C θ.val θ.property
    have hh := ENNReal.rpow_le_rpow he (by norm_num : 𝔦 ≤ 𝙖)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) $ by norm_num ,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq $ sub_nonneg.mpr C.variance_interval.le ] at hh
    apply hh.trans
    apply ENNReal.ofReal_mono
    unfold elementaryRMSConstant
    simp

theorem elementary_upper_low_smoothness (hs : 𝘒₂) (hn : 𝕱) :
    𝔓 ≤
      ENNReal.ofReal (elementaryRMSConstant C * max 𝔈
        (n ^ (-4 * C.smoothness / (d + 𝘊)))) := by
  simpa only [elementarySmoothness, min_eq_left hs] using elementary_rms_upper C hn
