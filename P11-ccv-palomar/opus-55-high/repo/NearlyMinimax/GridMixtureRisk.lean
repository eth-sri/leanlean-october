module

public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.LowMixtureProbability
public import NearlyMinimax.GridMixtureDerivative
public import NearlyMinimax.GridScorePath
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine original-model prior risk and centered score bounds for the grid experiment. -/
𝚴
𝚨


𝗃 𝔷 ἀ d k n η
theorem gridSampleField_coordinate_measurable d k n η
    ξ i :
    Measurable fun x => 𝔷 gridSampleField x ξ i :=
  𝘜 $ (measurable_pi_apply ξ).comp
    𝔷 gridSampleField_measurable

𝗇 𝔊 gridWindowCount d k
𝗇 𝔎 𝙎
𝗇 𝔐 𝔷 gridSampleField
𝗇 𝔒 𝔷 gridSampleField_coordinate_measurable
𝗇 𝔖 𝙇
𝗇 𝔬 v - 𝔎 * t
𝗇 𝔱 𝔖 × LowMixtureMarks 𝔊 n
def gridMixtureLaw (d k n : ℕ) (a v η t : ℝ) :
    Measure 𝔱 :=
  lowMixtureLaw (Measure.pi 𝘂) 𝔊 n
    a 𝔬 t 𝔐
    𝔒

def gridMixtureScore (d k n : ℕ) (a v η t : ℝ) :
    𝔱 → ℝ :=
  lowMixtureScore 𝔊 n a 𝔬 η 𝔐

𝗇 𝕭 𝚠
𝗃 𝕷 encodeDesignResponse ἀ (z.1, z.2.2)
def gridLiftedObservable (k : ℕ) (a : ℝ) (T : 𝕭) :
    𝔱 → ℝ :=
  fun z => T.val 𝕷 a

𝗇 𝕮 (T.property.comp $ encodeDesignResponse_measurable a ).comp
theorem gridLiftedObservable_measurable k a
    (T : 𝕭) : Measurable $ gridLiftedObservable k a T :=
  𝕮
    $ measurable_fst.prodMk $ measurable_snd.comp measurable_snd

𝗇 𝔚 𝔷 gridSampleField x
theorem gridSampleField_eq_latent d k n η x :
    𝔚 =
      latentRegression 𝔊 n η 𝖾 (gridSampleWeights d k n x) := by
  funext ξ i
  exact (𝔷 grid_latent_regression_eq x ξ i).symm

𝗇 𝕳 𝖥
𝗇 𝔄 (𝕳 + 2) * η ≤ P.ρ
𝗃 𝕶 ἀ C P k
𝗃 𝔶 𝕶 ἀ n η
𝗇 𝔲 𝔶 grid_response_positive t ξ x hη ht hfield hvariance i y
𝗇 𝔅 fun x ξ i y => (𝔲).le
𝗇 𝔇 P.v - 𝙎 * t
𝗃 𝔴 ἀ d k n P.a P.v η t
𝗇 𝔈 𝔴 gridMixtureLaw
𝗇 𝔉 Measure.pi 𝙮₁
𝗇 𝔍 t ∈ 𝗃
𝗇 𝔗 𝗼
𝗇 𝔘 𝔴 gridMixtureScore z
𝗇 𝔦 𝔴 gridMixtureScore
𝗇 𝔩 𝔴 gridPriorScoreEnergy
𝗇 𝔫 𝔎 ≤ P.ρ
𝗃 𝔳 𝕶 ἀ n η t hη ht hfield hvariance
𝗃 𝕬 ἀ _ _ _ _ _
𝗃 𝕸 ∫ z, ἀ ∂ 𝔈
section

variable (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C)

𝗇 𝔥 𝔶 grid_full_score_energy_integrable t ξ hη ht hfield hvariance
theorem gridMixtureConditionalEnergy_integrable k n η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫) :
    Integrable (lowMixtureConditionalScoreEnergy 𝔊 n P.a
      𝔇 η t 𝔐)
      𝔉 := by
  unfold lowMixtureConditionalScoreEnergy
  have hξ ξ :=
    (𝔥).const_mul
      $ activationProductPrior 𝔊 t ξ
  simpa only [gridFullScoreEnergy,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent] using
    integrable_finsetSum Finset.univ fun ξ _ => hξ ξ

theorem grid_mixture_probability k n η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫) :
    IsProbabilityMeasure 𝔈 := by
  let _ := cubeVolume_isProbability d
  exact 𝕬 lowMixtureLaw_probability _ _ _ P.a_pos.ne' ht
    𝔅

𝗇 𝔛 𝔳 gridMixtureConditionalEnergy_integrable
theorem grid_mixture_score_memLp k n η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫) :
    MemLp 𝔦 2
      𝔈 := by
  let _ := cubeVolume_isProbability d
  exact 𝕬 lowMixtureScore_memLp_two _ _ _ _ P.a_pos.ne' ht
    𝔅
    𝔛

theorem grid_mixture_score_centered k n η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫) :
    𝕸 𝔘 = 0 := by
  let _ := cubeVolume_isProbability d
  exact 𝕬 lowMixtureScore_centered _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => 𝔲)
    𝔛

theorem grid_mixture_score_energy k n η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫) :
     ∫ z, 𝔘 ^ 2
      ∂ 𝔈 = 𝔩 := by
  let _ := cubeVolume_isProbability d
  have hξ ξ :=
    𝔥
  simpa only [gridMixtureScore, gridMixtureLaw, gridPriorScoreEnergy,
    gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
    gridSampleField_eq_latent] using lowMixtureScore_sq_integral_eq_sum
      𝔉 𝔊 n
      P.a 𝔇 η t 𝔐
      𝔒 P.a_pos.ne' ht
      𝔅
       fun ξ => (hξ ξ).congr $ Filter.Eventually.of_forall fun x => by
        simp only [gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
          gridSampleField_eq_latent]

end

𝗇 𝔓 𝔳 grid_mixture_probability
𝗇 𝔠 𝖧₂
𝗇 𝔡 gridLiftedObservable k P.a T.val
𝗇 𝔪 C.varianceLower_pos.le.trans (T.property _).1
theorem grid_lifted_observable_memLp C
    (P : LowSmoothnessTernaryConstants C) k η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫)
    (T : 𝔠) :
    MemLp 𝔡 2 𝔈 := by
  let _ := 𝔓
  apply MemLp.of_bound (gridLiftedObservable_measurable k P.a T.val).aestronglyMeasurable
    $ effectiveVarianceUpper C
  apply Filter.Eventually.of_forall
  intro z
  change |T.val.val 𝕷 P.a| ≤ effectiveVarianceUpper C
  rw [abs_of_nonneg 𝔪]
  grind

𝗇 𝔙 encodeDesignResponse a 𝖮
𝗇 𝔨 𝙈
def gridStateRisk (k : ℕ) (a v η t : ℝ) (T : 𝕭)
    (ξ : Fin 𝔊 → Fin 3) (x : 𝔖) : ℝ :=
  ∑ y : 𝔨, finiteResponseLikelihood 𝔊 n a
    𝔬 𝔚 ξ y *
      (T.val 𝔙 - 𝔬) ^ 2

𝗇 𝕴 gridStateRisk k P.a P.v η t T.val ξ
𝗇 𝔧 𝕴
𝗇 𝕯 hp x y
theorem grid_state_risk_integrable C
    (P : LowSmoothnessTernaryConstants C) k η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫)
    (T : 𝔠) ξ :
    Integrable 𝔧
      𝔉 := by
  let _ := cubeVolume_isProbability d
  let V := 𝔇
  let B := (effectiveVarianceUpper C + |V|) ^ 2
  have hp x y :=
    (𝔳 grid_response_likelihood_pos x ξ y).le
  have hb z : (T.val.val z - V) ^ 2 ≤ B := by
    have hab : |T.val.val z| ≤ effectiveVarianceUpper C := by
      rw [𝗼₂]
      grind
    simpa only [sq_abs] using 𝗂 ((abs_sub (T.val.val z) V).trans $ add_le_add hab $ le_refl |V| ) 2
  have hm : Measurable 𝔧 := by
    apply Finset.measurable_sum
    intro y _
    exact (𝕬 finiteResponseLikelihood_measurable_comp
      𝔒 ξ y).mul
      $ ((T.val.property.comp $ encodeDesignResponse_measurable P.a ).comp
        $ measurable_id.prodMk measurable_const ).sub_const V |>.pow_const 2
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hnn : 0 ≤ 𝕴 x :=
    Finset.sum_nonneg fun y _ => mul_nonneg 𝕯 $ sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc
    _ ≤ ∑ y : 𝔨, finiteResponseLikelihood 𝔊 n P.a V
      𝔚 ξ y * B :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hb _) 𝕯
    _ = B := by
      rw [← Finset.sum_mul, 𝕬 finite_response_normalized _ P.a_pos.ne', one_mul]

𝗇 𝔏 (𝕳 + 68 * 𝕳 * 𝗞₁) * b ≤ C.holderBound
𝗇 𝔔 (𝚡₂).toReal
𝗇 𝔢 η = b / k ^ C.smoothness
𝗇 𝔣 gridLiftedObservable k P.a T.val z
𝗇 𝔮 ∫ z, (𝔣 - 𝔇) ^ 2 ∂ 𝔈
𝗃 𝔵 𝕶 ἀ η t hη ht hfield hvariance T
𝗇 𝕰 boundedEstimator_worstCaseRisk_ne_top C T
𝗃 𝕵 ἀ 𝔉 𝔊 n P.a 𝔇 t 𝔐 𝔒 P.a_pos.ne' ht 𝔅 _
theorem grid_mixture_risk_le_original_worstCase (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) η b t
    (hk : 𝗽₁) (hs1 : 𝘒₂) (hb : 𝘸)
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫)
    (hscale : 𝔢)
    (hholder : 𝔏)
    (T : 𝔠) :
    𝔮 ≤ 𝔔 := by
  let _ := cubeVolume_isProbability d
  have hξ ξ :=
    𝔵 grid_state_risk_integrable ξ
  unfold gridMixtureLaw
  rw [𝕵 lowMixtureLaw_nonneg_integral_sum ((gridLiftedObservable_measurable k P.a T.val).sub_const _ |>.pow_const 2)
    𝖸 hξ]
  calc
    _ ≤ ∑ ξ : Fin 𝔊 → Fin 3,
      activationProductPrior 𝔊 t ξ * 𝔔 := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · apply (ENNReal.ofReal_le_iff_le_toReal 𝕰).mp
        exact 𝕶 gridPathParameter_finite_risk_le_worstCase η b t ξ hk hs1 hb hη ht
          hfield hvariance hscale hholder T
      · exact Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht.1 ht.2 $ ξ j
    𝘿 := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]

def gridEncodedObservable (a : ℝ) (T : 𝕭) :
    𝔖 → 𝔨 → ℝ :=
  fun x y => T.val 𝔙

theorem gridEncodedObservable_measurable a (T : 𝕭) :
    Measurable $ gridEncodedObservable a T := by
  apply Measurable.of_eval
  intro y
  exact 𝕮
    $ measurable_id.prodMk measurable_const

𝗃 𝕹 ‖gridEncodedObservable ἀ T.val x‖ ≤ effectiveVarianceUpper C
theorem gridEncodedObservable_norm_le (C : ModelConstants d)
    a (T : 𝔠) x :
    𝕹 a := by
  apply (pi_norm_le_iff_of_nonneg $ C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le ).mpr
  intro y
  change |T.val.val 𝔙| ≤ effectiveVarianceUpper C
  rw [abs_of_nonneg 𝔪]
  grind

𝗇 𝔑 𝔵 grid_lifted_observable_memLp
𝗇 𝔜 gridEncodedObservable P.a T.val
𝗇 𝔰 𝕵 lowMixtureLaw_integral hi
theorem grid_mixture_mean_eq C
    (P : LowSmoothnessTernaryConstants C) k η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫)
    (T : 𝔠) :
    𝕸 𝔣 =
      𝔴 gridMixtureExpectation 𝔜 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔓
  have hi := (𝔑).integrable
    𝖠₄
  exact 𝔰

𝗇 𝔞 𝔳 grid_mixture_score_memLp
𝗇 𝔯 ∫ x, 𝔴 gridMixtureScoreObservable 𝔜 x ∂ 𝔉
theorem grid_mixture_score_observable_eq C
    (P : LowSmoothnessTernaryConstants C) k η t
    (hη : 𝔗) (ht : 𝔍)
    (hfield : 𝔄) (hvariance : 𝔫)
    (T : 𝔠) :
     ∫ z, 𝔣 * 𝔘
      ∂ 𝔈 =
      𝔯 := by
  let _ := cubeVolume_isProbability d
  have hi := (𝔑).integrable_mul
    𝔞
  simpa only [gridLiftedObservable, gridMixtureScore, gridMixtureLaw,
    gridMixtureScoreObservable, gridEncodedObservable, lowMixtureScore, Pi.mul_apply, mul_assoc,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField] using
    𝔰

section

variable {d n : ℕ}
    (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C)
    (k : ℕ)

𝗇 𝔟 n * (2 / 𝙦) ^ d ≤ 1
𝗇 𝔤 t ∈ Icc 0 1
𝗇 𝕱 gridUniformScoreBudget P k n η ≤ 1
𝗇 𝕲 hris t ht
/-- The complete actual-model score argument. All latent states obey the
original Hölder/moment class and all score and risk identities are derived. -/
theorem grid_prior_boundedEstimator_separation η b
    (hk : 𝗽₁) (hs1 : 𝘒₂) (hb : 𝘸) (hη : 𝔗)
    (hfield : 𝔄) (hvariance : 𝔫)
    (hscale : 𝔢)
    (hholder : 𝔏)
    (hmean : 𝔟) (hbudget : 𝕱)
    (T : 𝔠) :
    𝔎 ≤ 3 * Real.sqrt 𝔔 := by
  let r := Real.sqrt 𝔔
  let m := fun t => 𝔴 gridMixtureExpectation 𝔜
  let m' := fun t => 𝔯
  let sn := fun t => Real.sqrt 𝔩
  have hr : 𝘵₁ := Real.sqrt_nonneg _
  have hT := gridEncodedObservable_measurable P.a T.val
  have hTB : ∀ᵐ x ∂ 𝔉,
      𝕹 P.a :=
    Filter.Eventually.of_forall $ gridEncodedObservable_norm_le C P.a T
  have hderiv (t : ℝ) (ht : 𝔤) :=
    (𝔶 grid_mixture_expectation_hasDerivAt t (effectiveVarianceUpper C)
      hη ht hfield hvariance _ hT hTB).2
  have hderivI :=
    𝔶 grid_mixture_score_observable_intervalIntegrable (effectiveVarianceUpper C)
      hη hfield hvariance _ hT hTB
  have hscoreI :=
    𝔶 grid_sqrt_score_energy_intervalIntegrable hk hη hfield hvariance hmean
  have hris (t : ℝ) (ht : 𝔤) :
      𝔮 ≤ 𝘴₁ := by
    rw [ Real.sq_sqrt ENNReal.toReal_nonneg ]
    exact 𝕶 grid_mixture_risk_le_original_worstCase η b t hk hs1 hb hη ht
      hfield hvariance hscale hholder T
  have hderivBound t (ht : 𝔤) : |m' t| ≤ r * sn t := by
    let _ := 𝔓
    have h := probability_score_bound 𝔈
      𝔡 𝔦
      𝔇 r
      𝔑
      𝔞 hr
      𝔳 grid_mixture_score_centered 𝕲
    rw [𝔵 grid_mixture_score_observable_eq,
      𝔳 grid_mixture_score_energy] at h
    exact h
  have hbias t (ht : 𝔤) : |m t - 𝔇| ≤ r := by
    let _ := 𝔓
    have h := probability_mean_error_le 𝔈
      𝔡 𝔇 r
      𝔑 hr 𝕲
    rw [𝔵 grid_mixture_mean_eq] at h
    exact h
  have hsep := path_separation_le  𝖠₄  hderiv hderivI hscoreI
    hderivBound (hbias 0 𝖠₄ ) $ hbias 1 𝖠₄
  have hscoreBudget := 𝔶 grid_sqrt_score_energy_integral_le_one hk hη hfield
    hvariance hmean hbudget
  have he : |(P.v - 𝔎 * 1) - (P.v - 𝔎 * 0)| = 𝔎 := by
    simp
  nlinarith

𝗇 𝔭 𝔎 / 3
/-- Actual minimax RMS lower bound from the fully constructed grid prior. -/
theorem grid_prior_minimax_lower η b
    (hk : 𝗽₁) (hs1 : 𝘒₂) (hb : 𝘸) (hη : 𝔗)
    (hfield : 𝔄) (hvariance : 𝔫)
    (hscale : 𝔢)
    (hholder : 𝔏)
    (hmean : 𝔟) (hbudget : 𝕱) :
    ENNReal.ofReal 𝔭 ≤ 𝚢 := by
  have hnonneg : 0 ≤ 𝔭 := 𝖠₃
  have hlower : ENNReal.ofReal 𝔭 ^ 2 ≤ minimaxRisk C n := by
    rw [minimaxRisk_eq_inf_bounded C n]
    apply le_iInf
    intro T
    rw [← ENNReal.ofReal_pow hnonneg 2]
    apply (ENNReal.ofReal_le_iff_le_toReal 𝕰).mpr
    have hsep := 𝕶 grid_prior_boundedEstimator_separation η b hk hs1 hb hη
      hfield hvariance hscale hholder hmean hbudget T
    have hdiv : 𝔭 ≤ Real.sqrt 𝔔 := 𝖡₄
    have hsq := pow_le_pow_left₀ hnonneg hdiv 2
    simp_all
  have h := ENNReal.rpow_le_rpow hlower (by norm_num : 𝙋 ≤ 𝙖)
  have he : (ENNReal.ofReal 𝔭 ^ 2) ^ (𝙖 : ℝ) =
      ENNReal.ofReal 𝔭 := by
    rw [← ENNReal.rpow_natCast_mul]
    norm_num
  rw [he] at h
  exact h
