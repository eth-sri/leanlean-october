module

public import NearlyMinimax.Clipping
public import NearlyMinimax.RiskIdentity
public import RoughRegime.LowerMeasure
public import NearlyMinimax.ParametricConstants
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Two-point testing for the actual ternary-response regression submodel.
This file constructs probability densities and transfers testing to the
original observation space. No minimax rate is an assumed premise.
-/

𝚴
𝚮
𝚨
open RoughRegime.GeneralTesting RoughRegime.LowerMeasure

def labelBase : Measure $ Fin 3 := ENNReal.ofReal (1 / 3 : ℝ) • Measure.count

instance labelBase_isProbability : IsProbabilityMeasure labelBase := by
  constructor
  simp [labelBase]
  exact ENNReal.inv_mul_cancel  𝖠₄  𝖠₄

𝗃 𝔗 ἀ a 0 V
𝗇 𝔍 𝔗 ternaryMass y
def ternaryDensityLaw (a V : ℝ) (ha : 𝙞)
    (hp : ∀ y, 0 ≤ 𝔍) : DensityLaw labelBase where
  density y := 3 * 𝔍
  measurable := measurable_of_countable _
  integrable := Integrable.of_finite
  nonneg := Filter.Eventually.of_forall fun y => mul_nonneg  𝖠₄  $ hp y
  integral_one := by
    rw [labelBase, integral_smul_measure, integral_count]
    norm_num only [ENNReal.toReal_ofReal, smul_eq_mul]
    rw [← Finset.mul_sum, 𝔗 ternary_normalized ha]
    norm_num

𝗇 𝔄 (ternaryDensityLaw a V ha hp).measure
theorem ternaryDensityLaw_measure a V ha
    hp :
    𝔄 =
      Measure.count.withDensity fun y => ENNReal.ofReal 𝔍 := by
  unfold DensityLaw.measure ternaryDensityLaw labelBase
  rw [withDensity_smul_measure, ← withDensity_smul]
  · congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul 𝖠₄ ]
    ring
  fun_prop

theorem ternaryDensityLaw_map a V ha
    hp :
    (ternaryDensityLaw a V ha hp).measure.map (ternaryValue a) = 𝔗 ternaryMeasure := by
  rw [ternaryDensityLaw_measure, count_withDensity,
    Measure.map_sum (measurable_of_countable _).aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_dirac]

𝗇 𝔉 𝗅
𝗇 𝔟 uniformZeroParameter d a
𝗇 𝔚 𝔟 V ha.ne' hp
theorem ternary_submodel_admissible C
    (a V : ℝ) (ha : 𝙆) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (_hVa : V < 𝔉)
    (hfourth : 𝔉 * V ≤ C.fourthBound)
    hp :
    Admissible C 𝔚 := by
  let θ := 𝔚
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩
  · simp only [uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨𝖾, 𝗓₂, contDiffOn_const, ?_⟩
    rw [holderNorm_zero]
    exact zero_le
  · apply Filter.Eventually.of_forall
    intro x
    simp only [uniformZeroParameter]
    refine ⟨𝔗 ternaryMeasure_integrable _, 𝔗 ternaryMeasure_integrable _,
      𝔗 ternaryMeasure_integrable _, 𝔗 ternaryMeasure_mean ha.ne' hp, ?_, ?_⟩
    · simpa using 𝔗 ternaryMeasure_variance ha.ne' hp
    · have he := 𝔗 ternaryMeasure_fourthMoment ha.ne' hp
      simp_all

def encodeResponse (a : ℝ) :
    𝙈 × 𝙇 → 𝙌 :=
  fun z i => (z.2 i, ternaryValue a $ z.1 i )

𝗇 𝔒 measurable_of_countable $ ternaryValue a
theorem encodeResponse_measurable a :
    Measurable $ encodeResponse (d := d) (n := n) a := by
  apply Measurable.of_eval
  intro i
  exact (𝘜 measurable_snd).prodMk
    $ (𝔒).comp
      $ 𝘜 measurable_fst

𝗇 𝔇 𝔟 V ha hp
𝗇 𝔎 fun z => (z.2, ternaryValue a z.1)
𝗇 𝔓 (𝔄).prod $ cubeVolume d
theorem ternary_label_design_map a V ha
    hp :
    (𝔓).map
      𝔎 =
        observationLaw 𝔇 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔗 ternaryMeasure_isProbability ha hp
  rw [uniformZeroParameter_observationLaw]
  have h := Measure.map_prod_map 𝔄 (cubeVolume d)
    𝔒 measurable_id
  rw [ternaryDensityLaw_map, Measure.map_id] at h
  calc
    _ = ((𝔓).map
        $ Prod.map (ternaryValue a) id ).map Prod.swap := by
      rw [Measure.map_map measurable_swap
        $ (𝔒).prodMap measurable_id ]
      rfl
    _ = ((𝔗 ternaryMeasure).prod $ cubeVolume d ).map Prod.swap := 𝖤₄
    𝘿 := Measure.prod_swap

𝗇 𝔏 Measure.pi 𝘂
𝗃 𝔘 fun _ => ἀ
𝗇 𝔙 𝙮₁
𝗃 𝔢 ἀ (Fin 3) (Covariate d) $ Fin n
𝗃 𝔥 (Measure.pi 𝔘 ἀ).prod
𝗃 𝔡 sampleLaw ἀ n
theorem encodeResponse_measurePreserving a V ha
    hp :
    MeasurePreserving (encodeResponse a)
      (𝔥 𝔄
        𝔏)
      𝔡 𝔇 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔗 ternaryMeasure_isProbability ha hp
  let _ : IsProbabilityMeasure $ observationLaw 𝔇 := by
    rw [uniformZeroParameter_observationLaw]
    infer_instance
  have hsingle : MeasurePreserving 𝔎
      𝔓
      $ observationLaw 𝔇 :=
    ⟨measurable_snd.prodMk $ (measurable_of_countable _).comp measurable_fst ,
      ternary_label_design_map a V ha hp⟩
  let e := 𝔢 MeasurableEquiv.arrowProdEquivProdArrow
  have he := (𝔢 measurePreserving_arrowProdEquivProdArrow
    𝔘 𝔄 𝔙).symm e
  exact (measurePreserving_pi _ _ 𝔘 hsingle).comp he

𝗇 𝔜 3 / (2 * 𝔉)
def ternaryDensitySlope (a : ℝ) : Fin 3 → ℝ :=
  ![𝔜, -3 / 𝔉, 𝔜]

𝗇 𝔛 ![0, 3, 0]
theorem ternary_density_affine a V y :
    3 * 𝔍 = 𝔛 y + V * ternaryDensitySlope a y := by
  fin_cases y <;> simp [ternaryMass, ternaryDensitySlope] <;> ring

𝗇 𝔅 fun θ : {θ // 𝙟} => 𝚍₂
𝗇 𝔊 T.val $ encodeResponse a z
𝗇 𝔐 𝔥 P₀.measure ν
𝗇 𝔑 𝔥 P₁.measure ν
𝗇 𝔔 fun z => 𝔊 - V₀
𝗇 𝔖 fun z => 𝔊 - V₁
𝗇 𝔞 ternaryMass a 0
𝗃 𝔦 ∀ y, cf ≤ 3 * 𝔞 ἀ y
𝗃 𝔧 Filter.Eventually.of_forall $ ternary_density_affine a ἀ
𝗃 𝔠 fun z => T.val z - ἀ
/-- Actual two-point testing lower bound for the original regression minimax
problem. The premises are numerical legality and one-observation mass bounds,
not statistical risk or estimator assumptions. -/
theorem ternary_two_point_minimax_lower (C : ModelConstants d) (n : ℕ)
    (a V₀ V₁ cf Cf : ℝ) (ha : 𝙆) (hcf : 𝙻₁) (hCf : 0 ≤ Cf)
    (hV₀ : C.varianceLower ≤ V₀) (hV₀upper : V₀ ≤ C.varianceUpper)
    (hV₁ : C.varianceLower ≤ V₁) (hV₁upper : V₁ ≤ C.varianceUpper)
    (hVa₀ : V₀ < 𝔉) (hVa₁ : V₁ < 𝔉)
    (hfourth₀ : 𝔉 * V₀ ≤ C.fourthBound)
    (hfourth₁ : 𝔉 * V₁ ≤ C.fourthBound)
    (hmass₀ : 𝔦 V₀)
    (hmass₁ : 𝔦 V₁)
    (hslope : ∀ y, |ternaryDensitySlope a y| ≤ Cf)
    (hsmall : 𝙒 * Cf ^ 2 * (V₀ - V₁) ^ 2 / (4 * cf) ≤ 𝚡) :
    ENNReal.ofReal (|V₁ - V₀| / 4) ≤ 𝚢 := by
  have hp₀ : ∀ y, 0 ≤ 𝔞 V₀ y := by
    grind
  have hp₁ : ∀ y, 0 ≤ 𝔞 V₁ y := by
    grind
  let θ₀ := 𝔟 V₀ ha.ne' hp₀
  let θ₁ := 𝔟 V₁ ha.ne' hp₁
  have hθ₀ :=
    ternary_submodel_admissible C a V₀ ha hV₀ hV₀upper hVa₀ hfourth₀ hp₀
  have hθ₁ :=
    ternary_submodel_admissible C a V₁ ha hV₁ hV₁upper hVa₁ hfourth₁ hp₁
  let P₀ := ternaryDensityLaw a V₀ ha.ne' hp₀
  let P₁ := ternaryDensityLaw a V₁ ha.ne' hp₁
  let ν := 𝔏
  let _ := cubeVolume_isProbability d
  let _ : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure $ Measure.pi 𝔙 )
  let L := densityLawWithSeed ν $ iidDensityLaw P₀ n
  let R := densityLawWithSeed ν $ iidDensityLaw P₁ n
  have hH : hellingerSquared L R ≤ 𝚡 := by
    have hone := affine_hellinger_bound P₀ P₁ 𝔛 (ternaryDensitySlope a)
      V₀ V₁ cf Cf hcf hCf
      𝔧 V₀
      𝔧 V₁
      (Filter.Eventually.of_forall fun y => by rw [← ternary_density_affine]; simp_all )
      (Filter.Eventually.of_forall fun y => by rw [← ternary_density_affine]; simp_all )
      $ Filter.Eventually.of_forall hslope
    rw [hellinger_with_seed]
    exact (hellinger_iid_le P₀ P₁ n).trans
      $ (mul_le_mul_of_nonneg_left hone $ Nat.cast_nonneg n ).trans $ by
        grind
  have hL : L.measure = 𝔐 := by
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = 𝔑 := by
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  rw [minimaxRMS_eq_inf_sup_eLpNorm]
  apply le_iInf
  intro T
  have ht := two_point_rmse_lower L R (T.val ∘ encodeResponse a)
    (T.property.comp $ encodeResponse_measurable a ) V₀ V₁ hH
  rw [hL, hR] at ht
  have he₀ : eLpNorm 𝔔 2
      𝔐 =
      eLpNorm 𝔠 θ₀.variance 2 𝔡 θ₀ := eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      $ encodeResponse_measurePreserving a V₀ ha.ne' hp₀
  have he₁ : eLpNorm 𝔖 2
      𝔑 =
      eLpNorm 𝔠 θ₁.variance 2 𝔡 θ₁ := eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      $ encodeResponse_measurePreserving a V₁ ha.ne' hp₁
  change _ ≤ eLpNorm 𝔔 2 _ ∨
    _ ≤ eLpNorm 𝔖 2 _ at ht
  rw [he₀, he₁] at ht
  rcases ht with ht | ht
  · exact ht.trans $ le_iSup 𝔅 ⟨θ₀, hθ₀⟩
  · exact ht.trans $ le_iSup 𝔅 ⟨θ₁, hθ₁⟩

theorem ternaryDensitySlope_eq a y :
    ternaryDensitySlope a y = 3 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryDensitySlope, ternaryVarianceDerivative] <;> ring

𝗇 𝔈 n ^ (-(𝙖 : ℝ))
𝗃 𝔣 ἀ _ hm
𝗃 𝔤 ἀ _ hp
𝗃 𝔨 ἀ n hn
/-- The original statistical class has a positive root-n minimax RMS lower
bound for every sample size n>=1 and every smoothness/dimension regime.
The constants and the actual iid submodel are constructed, not assumed. -/
theorem parametric_minimax_lower (C : ModelConstants d) :
    ∃ c , 𝘝 ∧ ∀ n : ℕ, 𝗚 →
      ENNReal.ofReal (c * 𝔈) ≤ 𝚢 := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  refine ⟨P.delta / 2, div_pos P.delta_pos 𝖠₄ , ?_⟩
  intro n hn
  have hm := 𝔨 P.varianceMinus_mem
  have hp := 𝔨 P.variancePlus_mem
  have hb₀ := 𝔣 P.model_variance_bounds
  have hb₁ := 𝔤 P.model_variance_bounds
  have htest := ternary_two_point_minimax_lower C n P.a (P.varianceMinus n)
    (P.variancePlus n) P.cf P.Cf P.a_pos P.cf_pos P.Cf_pos.le
    hb₀.1 hb₀.2 hb₁.1 hb₁.2
    𝔣 P.variance_lt_square_of_mem 𝔤 P.variance_lt_square_of_mem
    𝔣 P.fourth_le_of_mem 𝔤 P.fourth_le_of_mem
    𝔣 P.density_lower 𝔤 P.density_lower
     fun y => by rw [ternaryDensitySlope_eq]; exact P.derivative_bound y
    𝔨 P.score_budget_reverse
  have hinv : 𝔈 = (Real.sqrt n)⁻¹ := by
    rw [Real.rpow_neg $ Nat.cast_nonneg n , ← Real.sqrt_eq_rpow]
  have hscale : |P.variancePlus n - P.varianceMinus n| / 4 =
       P.delta / 2 * 𝔈 := by
    rw [abs_of_pos 𝔨 P.separation_pos, P.separation n, hinv]
    ring
  simp_all
