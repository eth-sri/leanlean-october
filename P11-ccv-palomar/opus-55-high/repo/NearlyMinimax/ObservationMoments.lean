module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.Moments
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

/-! Response moments under the original covariate-dependent error model.
All localization bounds are derived from the actual observation measure. -/

𝛏
𝚮
𝚨

def responseSecondBound (C : ModelConstants d) : ℝ :=
  C.holderBound ^ 2 + C.varianceUpper

𝗃 𝔰 ἀ ^ 4
def responseFourthBound (C : ModelConstants d) : ℝ :=
  8 * (𝔰 C.holderBound + C.fourthBound)

section

𝛇

theorem responseSecondBound_pos :
    0 < responseSecondBound C := by
  have hv := C.varianceLower_pos.trans C.variance_interval
  unfold responseSecondBound
  positivity

theorem responseFourthBound_pos :
    0 < responseFourthBound C := by
  have h4 := lt_of_le_of_lt (sq_nonneg _) C.fourth_margin
  unfold responseFourthBound
  positivity

end

𝗇 𝔅 Measurable fun z : 𝚛 => (z.1, θ.regression z.1 + z.2)
𝗇 𝔈 θ.regression x + u
𝗇 𝔍 𝙟
𝗇 𝔑 𝘊₂
𝗃 𝔦 ἀ C θ hθ
𝗇 𝔓 𝔦 designLaw_isProbability
/-- Single-observation Tonelli disintegration for the model's actual law. -/
theorem observationLaw_lintegral_conditioning C
    (θ : RegressionParameter d) (hθ : 𝔍)
    g (hg : Measurable g) :
     ∫⁻ z, g z ∂observationLaw θ =
      ∫⁻ x, ∫⁻ u, g (x, 𝔈) ∂θ.errors x ∂designLaw θ := by
  let := 𝔓
  have hm : 𝔅 :=
    𝔑
  unfold observationLaw
  rw [lintegral_map' hg.aemeasurable hm.aemeasurable]
  simpa only [Function.comp_def] using Measure.lintegral_compProd $ hg.comp hm

𝗃 𝔴 Integrable ἀ $ observationLaw θ
/-- Single-observation Bochner disintegration, with integrability explicit. -/
theorem observationLaw_integral_conditioning
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ModelConstants d)
    θ (hθ : 𝔍)
    (g : Observation d → E) (hg : 𝔴 g) :
     ∫ z, g z ∂observationLaw θ =
      ∫ x, ∫ u, g (x, 𝔈) ∂θ.errors x ∂designLaw θ := by
  let := 𝔓
  have hm : 𝔅 :=
    𝔑
  unfold observationLaw at hg ⊢
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  simpa only [Function.comp_def] using Measure.integral_compProd $ hg.comp_measurable hm

𝗃 𝔱 fun u => ἀ
𝗃 𝔶 fun u => 𝔰 ἀ
section

variable (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (f)

𝗇 𝔫 𝔰 f
𝗇 𝔗 ((integrable_const 𝔫).add h4).const_mul 8
𝗇 𝔙 Integrable 𝔶 u μ
𝗇 𝔐 8 * (𝔫 + 𝔰 u)
𝗇 𝔞 (f + u) ^ 4
/-- A shift of an unbounded fourth-integrable error is fourth integrable. -/
theorem integrable_shift_fourth (h4 : 𝔙) :
    Integrable 𝔱 𝔞 μ := by
  have hd :=
    𝔗
  apply hd.mono' ((measurable_const.add measurable_id).pow_const 4).aestronglyMeasurable
  filter_upwards [] with u
  change ‖𝔞‖ ≤ 𝔐
  rw [Real.norm_eq_abs, abs_of_nonneg $ by positivity ]
  have hp := (show Even 4 by decide).add_pow_le (a := f) (b := u)
  grind

𝗇 𝔤 ∫ u : ℝ, 𝔞 ∂μ
theorem integral_shift_fourth_le H B (_hH : 𝖹₁) (hf : |f| ≤ H)
    (h4 : 𝔙)
    (hB : ∫ u : ℝ, 𝔰 u ∂μ ≤ B) :
    𝔤 ≤ 8 * (𝔰 H + B) := by
  have hd : Integrable 𝔱 𝔐 μ :=
    𝔗
  have hmono : 𝔤 ≤
      ∫ u : ℝ, 𝔐 ∂μ := by
    apply integral_mono (integrable_shift_fourth μ f h4) hd
    intro u
    have hp := (show Even 4 by decide).add_pow_le (a := f) (b := u)
    grind
  have hf4 : 𝔫 ≤ 𝔰 H := by
    calc 𝔫 = |f| ^ 4 := by grind
         _ ≤ 𝔰 H := pow_le_pow_left₀ (abs_nonneg f) hf 4
  rw [integral_const_mul, 𝖻₁ h4, integral_const] at hmono
  simp at hmono
  nlinarith

end

𝗇 𝔇 𝔰 z.2
𝗇 𝔉 𝙃
𝗇 𝔎 z.2 ^ 2
𝗇 𝔒 ENNReal.ofReal $ responseFourthBound C
𝗇 𝔘 ENNReal.ofReal $ responseSecondBound C
𝗇 𝔛 θ.regression x ^ 2
𝗃 𝔮 ∫⁻ z, ENNReal.ofReal ἀ ∂observationLaw θ
section

variable (C)
    (θ : RegressionParameter d)
    (hθ : 𝔍)

include hθ

𝗇 𝔚 𝔦 admissible_regression_value_bound x hx
theorem admissible_conditional_response_fourth :
    ∀ᵐ x ∂designLaw θ,
      Integrable 𝔶 𝔈 (θ.errors x) ∧
       ∫ u : ℝ, 𝔰 𝔈 ∂θ.errors x ≤ responseFourthBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  exact ⟨integrable_shift_fourth _ _ hm.2.2.1,
    integral_shift_fourth_le _ _ _ _ C.holderBound_pos.le
      𝔚 hm.2.2.1 hm.2.2.2.2.2⟩

𝗇 𝔠 ∫ u : ℝ, 𝔈 ^ 2 ∂θ.errors x
theorem admissible_conditional_response_second :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u => 𝔈 ^ 2) (θ.errors x) ∧
      𝔠 =
        𝔛 + θ.variance ∧
      𝔠 ≤ responseSecondBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  have h2 : MemLp 𝔱 u 2 $ θ.errors x :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hm.2.1
  have heq := response_second_moment_of_centered_error h2 hm.2.2.2.1 hm.2.2.2.2.1
    $ θ.regression x
  refine ⟨((memLp_const $ θ.regression x ).add h2).integrable_sq, heq, ?_⟩
  rw [heq]
  have hfsq : 𝔛 ≤ C.holderBound ^ 2 := by
    calc 𝔛 = |θ.regression x| ^ 2 := by simp
         _ ≤ C.holderBound ^ 2 := 𝗂 𝔚 2
  exact add_le_add hfsq hθ.2.2.2.2.2.2.1

𝗇 𝔨 ∫⁻ x, w x ∂designLaw θ
𝗃 𝔬 ∫⁻ z, w z.1 * ENNReal.ofReal ἀ ∂observationLaw θ
𝗃 𝔭 _ ≤ ∫⁻ x, w x * ἀ ∂designLaw θ
𝗃 𝔲 fun z => w z.1 * ENNReal.ofReal ἀ
/-- Arbitrary nonnegative design weights may localize the response fourth moment. -/
theorem observationLaw_weighted_fourth_le w (hw : Measurable w) :
    𝔬 𝔇 ≤
      𝔒 * 𝔨 := by
  rw [𝔦 observationLaw_lintegral_conditioning
    𝔲 𝔇
    $ (hw.comp measurable_fst).mul
      $ ENNReal.measurable_ofReal.comp $ measurable_snd.pow_const 4 ]
  calc
    𝔭 𝔒 := by
      apply lintegral_mono_ae
      filter_upwards [𝔦 admissible_conditional_response_fourth] with x hx
      rw [lintegral_const_mul (w x)
         𝖦₃ ]
      gcongr
      rw [← ofReal_integral_eq_lintegral_ofReal hx.1
        $ Eventually.of_forall fun u => 𝖠₃ ]
      exact ENNReal.ofReal_mono hx.2
    𝘿 := by rw [lintegral_mul_const _ hw, mul_comm]

theorem observationLaw_weighted_second_le w (hw : Measurable w) :
    𝔬 𝔎 ≤
      𝔘 * 𝔨 := by
  rw [𝔦 observationLaw_lintegral_conditioning
    𝔲 𝔎
    $ (hw.comp measurable_fst).mul
      $ ENNReal.measurable_ofReal.comp $ measurable_snd.pow_const 2 ]
  calc
    𝔭 𝔘 := by
      apply lintegral_mono_ae
      filter_upwards [𝔦 admissible_conditional_response_second] with x hx
      rw [lintegral_const_mul (w x)
         𝖦₃ ]
      gcongr
      rw [← ofReal_integral_eq_lintegral_ofReal hx.1
        $ Eventually.of_forall fun u => 𝖠₃ ]
      exact ENNReal.ofReal_mono hx.2.2
    𝘿 := by rw [lintegral_mul_const _ hw, mul_comm]

/-- The observed covariate has exactly the original design marginal. -/
theorem observationLaw_fst_measurePreserving :
    MeasurePreserving Prod.fst
      (observationLaw θ) $ designLaw θ := by
  let := 𝔓
  refine ⟨measurable_fst, ?_⟩
  have hm : 𝔅 :=
    𝔑
  unfold observationLaw
  rw [Measure.map_map measurable_fst hm]
  exact Measure.fst_compProd (designLaw θ) θ.errors

theorem observationLaw_fourth_lintegral_le :
    𝔮 𝔇 ≤
      𝔒 := by
  let := 𝔓
  simpa using 𝔦 observationLaw_weighted_fourth_le 𝔉 measurable_const

end

𝗃 𝔷 fun z : Observation d => ἀ
𝗇 𝔟 𝔷 𝔇
𝗃 𝕬 fun z => ENNReal.ofReal ἀ
theorem observationLaw_response_fourth_integrable C
    θ (hθ : 𝔍) :
    𝔴 𝔟 := by
  refine ⟨(measurable_snd.pow_const 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (fun z : Observation d => ‖ 𝔇 ‖ₑ) =
      𝕬 𝔇 := by
    funext z
    exact Real.enorm_of_nonneg 𝖠₃
  rw [heq]
  exact lt_of_le_of_lt 𝔦 observationLaw_fourth_lintegral_le ENNReal.ofReal_lt_top

𝗇 𝔩 fun z => 𝔇
theorem observationLaw_response_memLp_four C
    (θ : RegressionParameter d) (hθ : 𝔍) :
    MemLp Prod.snd 4 $ observationLaw θ := by
  apply (integrable_norm_rpow_iff
    measurable_snd.aestronglyMeasurable  𝖠₄  𝖢₄ ).mp
  have heq : (fun z : Observation d => ‖z.2‖ ^ (4 : 𝙉₁).toReal ) =
      𝔩 := by
    funext z
    calc
      |z.2| ^ 4 = |z.2| ^ 4 := Real.rpow_natCast ..
      _ = |𝔇| := (abs_pow z.2 4).symm
      _ = 𝔇 := abs_of_nonneg 𝖠₃
  rw [heq]
  exact 𝔦 observationLaw_response_fourth_integrable

theorem observationLaw_response_memLp_two C
    (θ : RegressionParameter d) (hθ : 𝔍) :
    MemLp Prod.snd 2 $ observationLaw θ := by
  let := 𝔦 observationLaw_isProbability
  exact (𝔦 observationLaw_response_memLp_four).mono_exponent 𝖠₄

𝗇 𝔄 (Prod.fst ⁻¹' A).indicator
𝗇 𝔪 designLaw θ A
𝗃 𝔯 fun z => A.indicator 𝔉 z.1 * ENNReal.ofReal ἀ
𝗃 𝔵 𝔦 ἀ (A.indicator 𝔉) $ measurable_const.indicator hA
theorem observationLaw_localized_fourth_lintegral_le C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
     ∫⁻ z, ENNReal.ofReal
      (𝔄 𝔟 z)
      ∂observationLaw θ ≤ 𝔒 * 𝔪 := by
  have hh := 𝔵 observationLaw_weighted_fourth_le
  have heq : 𝔯 𝔇 = fun z => ENNReal.ofReal
      $ 𝔄 𝔩 z := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  simp_all

𝗇 𝔏 𝔄 𝔷 𝔎 z
𝗇 𝔢 𝔄 (fun z => 𝔎) z
theorem observationLaw_localized_second_lintegral_le C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
    𝔮 𝔏 ≤ 𝔘 * 𝔪 := by
  have hh := 𝔵 observationLaw_weighted_second_le
  have heq : 𝔯 𝔎 = 𝕬 𝔢 := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  simp_all

𝗇 𝔊 𝘐₂ A
𝗇 𝔔 𝔦 observationLaw_response_memLp_two
𝗇 𝔜 measure_ne_top (designLaw θ) A
𝗇 𝔣 (𝔔).integrable_sq.indicator $ measurable_fst hA
𝗇 𝔥 ∫ z, 𝔏 ∂observationLaw θ
𝗃 𝔳 ἀ C * 𝔊
theorem observationLaw_localized_second_integral_le C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
    𝔥 ≤ 𝔳 responseSecondBound := by
  have hi := 𝔣
  have hh := 𝔦 observationLaw_localized_second_lintegral_le A hA
  rw [← ofReal_integral_eq_lintegral_ofReal hi $ Eventually.of_forall fun z => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _ ] at hh
  have hb := responseSecondBound_pos C
  let := 𝔓
  have heq : 𝔘 * 𝔪 =
      ENNReal.ofReal 𝔳 responseSecondBound := by
    rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal 𝔜]
  simp_all

𝗃 𝔧 ∫ z, 𝔄 ἀ z ∂observationLaw θ
theorem observationLaw_localized_fourth_integral_le C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
    𝔧 𝔟 ≤ 𝔳 responseFourthBound := by
  have hi := (𝔦 observationLaw_response_fourth_integrable).indicator
    $ measurable_fst hA
  have hh := 𝔦 observationLaw_localized_fourth_lintegral_le A hA
  rw [← ofReal_integral_eq_lintegral_ofReal hi $ Eventually.of_forall fun z => Set.indicator_nonneg fun _ _ => by positivity _ ] at hh
  have hb := responseFourthBound_pos C
  let := 𝔓
  have heq : 𝔒 * 𝔪 =
      ENNReal.ofReal 𝔳 responseFourthBound := by
    rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal 𝔜]
  simp_all

𝗇 𝔖 hi.indicator $ measurable_fst hA
𝗇 𝔡 fun z => 2 * (1 + 𝔎)
theorem observationLaw_localized_response_energy_le C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
     ∫ z, 𝔄
      (fun z : Observation d => (1 + |z.2|) ^ 2) z ∂observationLaw θ ≤
       2 * (1 + responseSecondBound C) * 𝔊 := by
  let := 𝔦 observationLaw_isProbability
  have hs : MemLp (fun z => |z.2|) 2 $ observationLaw θ := by
    simpa only [Real.norm_eq_abs] using (𝔔).norm
  have hi : Integrable (fun z => (1 + |z.2|) ^ 2)
      $ observationLaw θ := ((memLp_const 𝙠).add hs).integrable_sq
  have hd : 𝔴 𝔡 :=
    ((integrable_const 1).add
      (𝔔).integrable_sq).const_mul 2
  have hb := integral_mono 𝔖
    (hd.indicator $ measurable_fst hA ) fun z => by
      apply Set.indicator_le_indicator
      have hab := sq_nonneg $ 1 - |z.2|
      nlinarith [sq_abs z.2]
  have heq : (fun z => 𝔄
      𝔡 z) =
       fun z => 2 * (𝔄 (fun _ => 𝙠) z +
        𝔢) := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  rw [heq, integral_const_mul,
    integral_add ((integrable_const 1).indicator $ measurable_fst hA )
      𝔣] at hb
  have hI : 𝔧 𝔉 = 𝔊 := by
    rw [integral_indicator_const 1 $ measurable_fst hA ]
    simp
    exact (𝔦 observationLaw_fst_measurePreserving).measureReal_preimage
      hA.nullMeasurableSet
  have hb2 := 𝔦 observationLaw_localized_second_integral_le A hA
  nlinarith

/-- Exact localized first moment, with the covariate-dependent conditional law. -/
theorem observationLaw_localized_first_integral C
    (θ : RegressionParameter d) (hθ : 𝔍)
    A (hA : MeasurableSet A) :
    𝔧 Prod.snd =
      ∫ x, A.indicator θ.regression x ∂designLaw θ := by
  let := 𝔦 observationLaw_isProbability
  have hi := (𝔔).integrable 𝖠₄
  rw [𝔦 observationLaw_integral_conditioning _
    𝔖]
  apply integral_congr_ae
  filter_upwards [hθ.2.2.2.2.2.2.2] with x hx
  by_cases hxa : x ∈ A
  · simp [hxa, 𝖻₁ hx.1, hx.2.2.2.1]
  simp_all

/-- Exact localized second moment; no marginal error distribution is introduced. -/
theorem observationLaw_localized_second_integral C
    θ (hθ : 𝔍)
    A (hA : MeasurableSet A) :
    𝔥 =
      ∫ x, A.indicator (fun x => 𝔛 + θ.variance) x ∂designLaw θ := by
  have hi := (𝔔).integrable_sq
  rw [𝔦 observationLaw_integral_conditioning _
    𝔖]
  apply integral_congr_ae
  filter_upwards [𝔦 admissible_conditional_response_second] with x hx
  by_cases hxa : x ∈ A
  all_goals simp_all
