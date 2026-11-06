module

public import NearlyMinimax.LowSmoothnessConstants
public import NearlyMinimax.ParametricLower
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! # Actual probability laws of the low-smoothness mixture

The finite response labels encode the original real response experiment.
This file proves the law identification and transfers its risks to the
original model; it introduces no statistical risk premise.
-/

𝚴
𝚮

𝚨

𝗇 𝔈 ternaryMass a (F x) V y
𝗇 𝔗 𝘬
𝗃 𝔤 ἀ a V F hF
𝗇 𝔙 𝔤 ternaryMass_measurable_comp y
𝗇 𝔟 ∑ y : Fin 3, ENNReal.ofReal 𝔈 • Measure.dirac y
def responseIndexKernel [MeasurableSpace α] (a V : ℝ)
    (F : 𝔗) (hF : Measurable F) : Kernel α $ Fin 3 where
  toFun x := 𝔟
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun y _ =>
      (ENNReal.measurable_ofReal.comp 𝔙).mul_const _

theorem responseIndexKernel_apply [MeasurableSpace α] a V
    F hF (x : α) :
    𝔤 responseIndexKernel x =
      𝔟 := rfl

𝗇 𝔏 𝔤 responseIndexKernel
𝗇 𝔛 ∀ x y, 0 ≤ 𝔈
theorem responseIndexKernel_markov [MeasurableSpace α] a V
    (F : 𝔗) hF (ha : 𝙞)
    (hp : 𝔛) :
    IsMarkovKernel 𝔏 := by
  constructor
  intro x
  constructor
  simp only [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => hp x y , ternary_normalized a (F x) V ha]
  simp

𝗇 𝔅 𝔤 uniformTernaryParameter ha hp
𝗇 𝔯 (z.1, ternaryValue a z.2)
𝗃 𝔴 fun z => ἀ
𝗇 𝔓 𝔴 𝔯
𝗇 𝔔 𝔤 responseIndexKernel_markov ha hp
𝗇 𝔚 (measurable_of_countable _).comp measurable_snd
𝗇 𝔧 (cubeVolume d).compProd 𝔏
𝗇 𝔨 (z.1, F z.1 + z.2)
/-- Encoding the genuine conditional index law gives the original real-response
observation law, including its covariate-dependent error kernel. -/
theorem uniformTernaryParameter_observation_index_map
    a V F hF ha
    hp :
    (𝔧).map
      𝔓 =
      observationLaw 𝔅 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔔
  let _ := 𝔤 ternaryErrorKernel_markov ha hp
  have hencode : Measurable fun z : Covariate d × Fin 3 => 𝔯 :=
    measurable_fst.prodMk 𝔚
  have hreal : Measurable fun z : 𝚛 => 𝔨 :=
    measurable_fst.prodMk $ (hF.comp measurable_fst).add measurable_snd
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw 𝔅).compProd
    𝔤 ternaryErrorKernel).map 𝔴 𝔨) s
  rw [Measure.map_apply hreal hs]
  simp only [designLaw, uniformTernaryParameter, ENNReal.ofReal_one, withDensity_const, one_smul]
  rw [Measure.compProd_apply $ hs.preimage hencode , Measure.compProd_apply $ hs.preimage hreal ]
  apply lintegral_congr
  intro x
  simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : (x, 𝗐₂) ∈ s <;> simp [h]

𝗇 𝔰 F $ x i
𝗇 𝔄 ∏ i, ternaryMass a 𝔰 V (y i)
𝗇 𝔇 𝙈
𝗇 𝔖 𝔰
𝗇 𝔘 𝚅₁
𝗇 𝔡 ∑ y : 𝔇, ENNReal.ofReal 𝔄 • Measure.dirac y
/-- The genuine conditional law of all finite response labels. -/
def responseSampleIndexKernel [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    (F : 𝔗) (hF : Measurable F) : Kernel 𝔘 𝔇 where
  toFun x := 𝔡
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro y _
    apply Measurable.mul_const
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ fun i _ =>
      ternaryMass_measurable_comp a V (fun x : 𝔘 => 𝔖)
        (hF.comp $ measurable_pi_apply i ) $ y i

𝗃 𝔣 ἀ n a V F hF
𝗇 𝔍 𝔣 responseSampleIndexKernel
𝗇 𝔎 𝔣 responseSampleIndexKernel_markov ha hp
𝗇 𝔑 𝖮
𝗇 𝔜 𝔣 responseSampleIndexKernel x
𝗇 𝔥 hp $ x i
𝗇 𝔬 ternaryMass a 𝔖 V y
section

variable [MeasurableSpace α]

theorem responseSampleIndexKernel_apply n a V (F : 𝔗) hF x :
    𝔜 =
      𝔡 := rfl

theorem responseSampleIndexKernel_markov n a V (F : 𝔗) hF (ha : 𝙞)
    (hp : 𝔛) :
    IsMarkovKernel 𝔍 := by
  constructor
  intro x
  constructor
  simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => Finset.prod_nonneg
       fun i _ => 𝔥 $ y i , ← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

𝗇 𝔐 fun i => (z.1 i, z.2 i)
𝗇 𝔩 𝘫
𝗇 𝔪 𝔴 𝔐
/-- The sample kernel, with designs drawn independently, is the same law as
independent pairs from the one-observation kernel. -/
theorem responseSampleIndexKernel_joint_map (μ : Measure α) [IsProbabilityMeasure μ]
    n a V F hF (ha : 𝙞)
    (hp : 𝔛) :
    ((Measure.pi 𝔩).compProd
      𝔍).map
      𝔪 =
      Measure.pi fun _ => μ.compProd 𝔏 := by
  let _ := 𝔔
  let _ := 𝔎
  have hm : Measurable fun z : 𝔘 × 𝔇 =>
      𝔐 := 𝖦₃
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm $ MeasurableSet.univ_pi hs ,
    Measure.compProd_apply $ (MeasurableSet.univ_pi hs).preimage hm ]
  have hinner x :
      𝔜
        (Prod.mk x ⁻¹' 𝔪 ⁻¹' Set.pi Set.univ s) =
        ∏ i, ∑ y : Fin 3, ENNReal.ofReal 𝔬 *
          (s i).indicator 1 (x i, y) := by
    simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply]
    simp_rw [ENNReal.ofReal_prod_of_nonneg fun i _ => 𝔥 _ ]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : ∀ i, (x i, y i) ∈ s i
    · simp_all
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [Finset.prod_mul_distrib]
      have hzero : ∏ j, (s j).indicator (1 : α × Fin 3 → 𝙉₁) (x j, y j) = 0 :=
        𝗈₁ $ Set.indicator_of_notMem hi _
      simp_all
  simp_rw [hinner]
  let G := fun i x =>
    ∑ y : Fin 3, ENNReal.ofReal 𝔈 * (s i).indicator 1 𝔑
  have hG : ∀ i, Measurable $ G i := by
    intro i
    exact Finset.measurable_sum _ fun y _ =>
      (ENNReal.measurable_ofReal.comp 𝔙).mul
        $ (Measurable.indicator measurable_const $ hs i ).comp $ measurable_id.prodMk measurable_const
  rw [𝗒]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval 𝔩 i).lintegral_comp $ hG i ]
  rw [Measure.compProd_apply $ hs i ]
  apply lintegral_congr
  intro x
  simp only [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ $ (hs i).preimage measurable_prodMk_left ]
  rfl

end

/-- Encode all finite response labels as the paper's real observations. -/
def encodeDesignResponse (a : ℝ) :
    𝙇 × 𝔇 → 𝙌 :=
  fun z i => (z.1 i, ternaryValue a $ z.2 i )

𝗃 𝔲 ἀ (d := d) (n := n) a
theorem encodeDesignResponse_measurable a :
    Measurable 𝔲 encodeDesignResponse := (encodeResponse_measurable a).comp measurable_swap

𝗇 𝔉 Measure.pi 𝙮₁
𝗇 𝔠 sampleLaw 𝔅 n
𝗇 𝔭 (𝔉).compProd 𝔍
/-- Identification with the complete iid sample law of the original model. -/
theorem uniformTernaryParameter_sample_index_map
    n a V F hF ha
    hp :
    (𝔭).map (encodeDesignResponse a) =
      𝔠 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔔
  let _ := 𝔎
  have hsingle : MeasurePreserving
      𝔓
      𝔧
      $ observationLaw 𝔅 :=
    ⟨measurable_fst.prodMk 𝔚,
      𝔤 uniformTernaryParameter_observation_index_map ha hp⟩
  let _ : IsProbabilityMeasure $ observationLaw 𝔅 := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ fun _ : Fin n => hsingle ).map_eq
  rw [← responseSampleIndexKernel_joint_map (cubeVolume d) n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  all_goals fun_prop

/-- Genuine finite conditional integrals, with no density representation
assumption, equal the likelihood sums used by the score proof. -/
theorem responseSampleIndexKernel_integral [MeasurableSpace α]
    n a V (F : 𝔗) hF x
    (hp : ∀ i y, 0 ≤ 𝔬)
    (H : 𝔇 → ℝ) :
     ∫ y, H y ∂𝔜 =
      ∑ y, 𝔄 * H y := by
  rw [responseSampleIndexKernel_apply, integral_finsetSum_measure]
  · simp
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_ofReal $ Finset.prod_nonneg fun i _ => 𝚗₁ ]
  · intro y _
    let _ := (Measure.dirac y).smul_finite
      (c := ENNReal.ofReal 𝔄) ENNReal.ofReal_ne_top
    exact Integrable.of_finite

𝗇 𝔮 encodeDesignResponse a 𝔑
/-- Bounded data-observable expectations in the genuine original sample law
are exactly the design-integrated finite likelihood expectations. -/
theorem uniformTernaryParameter_sample_integral
    n a V F hF ha
    hp
    H (hH : Measurable H)
    B (hB : ∀ z, |H z| ≤ B) :
     ∫ z, H z ∂𝔠 =
      ∫ x, ∑ y : 𝔇,
        𝔄 * H 𝔮
        ∂ 𝔉 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔎
  have hm := 𝔲 encodeDesignResponse_measurable
  rw [← 𝔣 uniformTernaryParameter_sample_index_map ha hp,
    integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hi : Integrable (fun z => H 𝗟₁)
      𝔭 :=
    (integrable_const B).mono' (hH.comp hm).aestronglyMeasurable
      $ Filter.Eventually.of_forall fun z => 𝖤₄
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    𝔣 responseSampleIndexKernel_integral x (fun i y => 𝔥 y) _

𝗇 𝔫 (T.val z - V) ^ 2
/-- Exact identification of the finite likelihood risk with the original
model's ENNReal mean-squared risk for every bounded measurable estimator. -/
theorem uniformTernaryParameter_risk_formula
    a V F hF ha
    hp
    (T : 𝚠) B (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : 𝔇,
      𝔄 *
        (T.val 𝔮 - V) ^ 2
      ∂ 𝔉) =
      meanSquaredRisk T 𝔅 := by
  let _ := cubeVolume_isProbability d
  let _ := 𝔎
  let _ : IsProbabilityMeasure 𝔠 := by
    rw [← 𝔣 uniformTernaryParameter_sample_index_map ha hp]
    infer_instance
  have hm := (T.property.sub_const V).pow_const 2
  have hbound z : |𝔫| ≤ (B + |V|) ^ 2 := by
    rw [𝗤]
    simpa only [sq_abs] using 𝗂 ((abs_sub (T.val z) V).trans $ add_le_add (hB z) $ le_refl |V| ) 2
  have hint : Integrable 𝔴 𝔫
      𝔠 :=
    (integrable_const $ (B + |V|) ^ 2 ).mono' hm.aestronglyMeasurable
      $ Filter.Eventually.of_forall fun z => 𝖤₄
  rw [← 𝔣 uniformTernaryParameter_sample_integral ha hp _ hm _ hbound]
  exact ofReal_integral_eq_lintegral_ofReal hint
    $ Filter.Eventually.of_forall fun z => sq_nonneg _

section

𝛇

𝗇 𝔊 P.v - 𝙎 * t
𝗇 𝔱 indexedGridField d k η ξ
𝗇 𝔒 fun ξ i => 𝔱 $ x i
𝗇 𝔞 finiteResponseLikelihood (gridWindowCount d k) n P.a 𝔊 𝔒 ξ y
𝗃 𝔢 ∫ x, ∑ y : 𝔇, 𝔞 * (ἀ (encodeDesignResponse P.a 𝔑) - 𝔊) ^ 2 ∂ 𝔉
𝗃 𝔳 ἀ C P k η t ξ hη ht hfield hvariance
/-- Exact risk formula for every concrete grid-prior state. -/
theorem gridPathParameter_risk_formula
    P
    k η t ξ
    hη ht
    hfield hvariance
    T B (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal 𝔢 T.val =
      meanSquaredRisk T 𝔳 gridPathParameter := by
  have hf x :=
    (𝙼₂ x).trans 𝖥₃
  have hp x y :=
    P.c_pos.le.trans $ (P.path_legality η t _ ht hvariance $ hf x ).2.2.1 y
  simpa only [gridPathParameter, LowSmoothnessTernaryConstants.pathParameter,
    LowSmoothnessTernaryConstants.variancePath, finiteResponseLikelihood] using
    uniformTernaryParameter_risk_formula P.a 𝔊
      𝔱 (indexedGridField_continuous d k η ξ).measurable
      P.a_pos.ne' hp T B hB

𝗇 𝔦 𝖥
/-- The prior risk contribution of every latent state is controlled by the
original bounded estimator's worst-case risk. -/
theorem gridPathParameter_finite_risk_le_worstCase
    (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) η b t ξ
    (hk : 𝗽₁) (hs1 : 𝘒₂) (hb : 𝘸)
    (hη : 𝗼) (ht : t ∈ 𝗃)
    (hfield : (𝔦 + 2) * η ≤ P.ρ) (hvariance : 𝙎 ≤ P.ρ)
    (hscale : η = b / k ^ C.smoothness)
    (hholder : (𝔦 + 68 * 𝔦 * 𝗞₁) * b ≤ C.holderBound)
    (T : 𝖧₂) :
    ENNReal.ofReal 𝔢 T.val.val ≤ 𝚡₂ := by
  have hB z : |T.val.val z| ≤ effectiveVarianceUpper C := by
    rw [𝗼₂]
    grind
  rw [𝔳 gridPathParameter_risk_formula T.val _ hB]
  exact le_iSup (fun θ : {θ // 𝙟} => meanSquaredRisk T.val θ.val)
    ⟨_, gridPathParameter_admissible C P k η b t ξ hk hs1 hb hη ht hfield
      hvariance hscale hholder⟩

/-- Clipped estimators have finite genuine worst-case risk, independently of
which admissible parameter realizes that risk. -/
theorem boundedEstimator_worstCaseRisk_ne_top (T : 𝖧₂) : 𝚡₂ ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro θ
  exact boundedEstimator_risk_le_diameter C T θ.val θ.property
