module

public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.LowMixtureLaw
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine normalized high-prior observation laws. Positivity of the raw
 density makes every raw state a probability experiment; the exceptional
 mass-concentration event is not needed for probability normalization. -/
𝚴
𝚮
𝚨
𝚱
𝚩

𝗇 𝔈 𝚃₂
theorem highRawDensity_integrable_of_interval p
    (hp : Measurable p) (a b : ℝ) (ha : 𝙆)
    (hb : 𝔈) :
    Integrable p $ cubeVolume d := by
  let _ := cubeVolume_isProbability d
  apply (integrable_const b).mono' hp.aestronglyMeasurable
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg $ ha.le.trans hx.1 ]
  exact hx.2

𝗇 𝔜 highRawDensity_integrable_of_interval p hp a b ha hb
𝗃 𝔢 hb.mono fun x hx => ἀ
theorem highRawDensityMass_mem_Icc p
    (hp : Measurable p) a b (ha : 𝙆)
    (hb : 𝔈) :
    highRawDensityMass p ∈ 𝘔₂ := by
  let _ := cubeVolume_isProbability d
  have hi := 𝔜
  constructor
  · simpa [highRawDensityMass] using
      integral_mono_ae (integrable_const a) hi 𝔢 hx.1
  · simpa [highRawDensityMass] using
      integral_mono_ae hi (integrable_const b) 𝔢 hx.2

𝗇 𝔖 fun x => ENNReal.ofReal $ highNormalizedDensity p x
𝗇 𝔄 (cubeVolume d).withDensity 𝔖
theorem normalizedDensityTernaryParameter_design_probability
    p (hp : Measurable p) a b (ha : 𝙆)
    (hb : 𝔈) :
    IsProbabilityMeasure 𝔄 := by
  let _ := cubeVolume_isProbability d
  have hm := highRawDensityMass_mem_Icc p hp a b ha hb
  constructor
  simpa using highNormalizedDensity_normalized p 𝔜
    (hb.mono fun x hx => ha.le.trans hx.1) $ ha.trans_le hm.1

𝗇 𝔏 responseSampleIndexKernel n a V F hF
𝗃 𝔛 fun _ : Fin n => ἀ
section

variable (p)
    (hdesign : IsProbabilityMeasure 𝔄)

include hdesign

𝗇 𝔅 normalizedDensityTernaryParameter p F a V hF ha hp
𝗇 𝔎 (z.1, F z.1 + z.2)
𝗇 𝔟 (z.1, ternaryValue a z.2)
𝗇 𝔑 fun z => 𝔟
𝗇 𝔓 (measurable_of_countable _).comp measurable_snd
𝗃 𝔚 ἀ a V F hF
𝗇 𝔗 (𝔄).compProd 𝔚 responseIndexKernel
𝗇 𝔞 fun z => 𝔎
theorem normalizedDensityTernaryParameter_observation_index_map
    a V F hF ha
    hp :
    (𝔗).map
      𝔑 =
      observationLaw 𝔅 := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  let _ := 𝔚 responseIndexKernel_markov ha hp
  let _ := 𝔚 ternaryErrorKernel_markov ha hp
  have hencode : Measurable fun z : Covariate d × Fin 3 => 𝔟 :=
    measurable_fst.prodMk 𝔓
  have hreal : Measurable fun z : 𝚛 => 𝔎 :=
    measurable_fst.prodMk $ (hF.comp measurable_fst).add measurable_snd
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw 𝔅).compProd
    𝔚 ternaryErrorKernel).map 𝔞) s
  rw [Measure.map_apply hreal hs]
  change _ = ((𝔄).compProd 𝔚 ternaryErrorKernel) (𝔞 ⁻¹' s)
  rw [Measure.compProd_apply $ hs.preimage hencode , Measure.compProd_apply $ hs.preimage hreal ]
  apply lintegral_congr
  intro x
  simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : (x, 𝗐₂) ∈ s <;> simp [h]

theorem normalizedDensityTernaryParameter_sample_index_map
    n a V F hF ha
    hp :
    ((Measure.pi fun _ => 𝔄 ).compProd
      𝔏).map (encodeDesignResponse a) =
      sampleLaw 𝔅 n := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  let _ := 𝔚 responseIndexKernel_markov ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hsingle : MeasurePreserving
      𝔑
      𝔗
      $ observationLaw 𝔅 :=
    ⟨measurable_fst.prodMk 𝔓,
      normalizedDensityTernaryParameter_observation_index_map p hdesign a V F hF ha hp⟩
  let _ : IsProbabilityMeasure $ observationLaw 𝔅 := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ 𝔛 hsingle).map_eq
  rw [← responseSampleIndexKernel_joint_map 𝔄 n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  all_goals fun_prop

end

𝗃 𝔡 ἀ $ z.1 i
𝗇 𝔇 ∏ i, ternaryMass a 𝔡 F V (z.2 i)
𝗇 𝔘 F $ x i
𝗇 𝔉 fun x y => ENNReal.ofReal $ ∏ i, ternaryMass a 𝔘 V (y i)
𝗇 𝔍 𝙈
𝗇 𝔒 𝚅₁
𝗃 𝔙 Finset.measurable_prod _ fun i _ => ternaryMass_measurable_comp a V (fun x : ἀ => 𝔘) (hF.comp $ measurable_pi_apply i ) $ y i
𝗃 𝔠 fun z : ἀ × 𝔍 => ENNReal.ofReal 𝔇
theorem responseSampleIndexKernel_eq_withDensity [MeasurableSpace α]
    n a V F hF :
    𝔏 =
      (Kernel.const 𝔒 Measure.count).withDensity
        𝔉 := by
  have hq : Measurable 𝔠 𝔒 := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact 𝔙 𝔒
  ext x : 1
  rw [Kernel.withDensity_apply _ hq]
  simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseSampleIndexKernel_apply]

𝗇 𝔐 fun x => ∏ i, f (x i)
𝗃 𝔣 (s ἀ).indicator f
/-- Density tensorization for a finite iid product, proved on measurable boxes. -/
theorem probability_pi_withDensity [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] f (hf : Measurable f)
    (hprob : IsProbabilityMeasure $ μ.withDensity f ) n :
    Measure.pi (fun _ => μ.withDensity f) =
      (Measure.pi 𝔛 μ).withDensity 𝔐 := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ $ MeasurableSet.univ_pi hs , ← lintegral_indicator]
  · have he x :
        (Set.pi Set.univ s).indicator 𝔐 x =
          ∏ i, 𝔣 i (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp_all
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, 𝔣 j (x j) = 0 :=
          𝗈₁ $ Set.indicator_of_notMem hi f
        simp_all
    simp_rw [he]
    let G := fun i => 𝔣 i
    have hG := fun i => hf.indicator $ hs i
    rw [𝗒]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval 𝘫 i).lintegral_comp $ hG i ]
    aesop
  · exact MeasurableSet.univ_pi hs

𝗇 𝔊 𝙇
def highSampleLikelihood (n : ℕ) (a V : ℝ)
    (p F : 𝙀) (z : 𝔊 × 𝔍) : ℝ :=
  (∏ i, 𝔡 p) / highRawDensityMass p ^ n *
    𝔇

𝗇 𝔔 fun i _ => hpn i
/-- Exact iid sample density with the raw mass raised to the sample size. -/
theorem highSample_index_density (n : ℕ) p F
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ)
    (hdesign : IsProbabilityMeasure 𝔄)
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq0 : 𝗨) :
     (Measure.pi 𝔛 𝔄).compProd
      𝔏 =
    ((Measure.pi 𝘂).prod
      Measure.count).withDensity
         fun z => ENNReal.ofReal $ highSampleLikelihood n a V p F z := by
  let _ := cubeVolume_isProbability d
  have hf : Measurable 𝔖 :=
    ENNReal.measurable_ofReal.comp $ highNormalizedDensity_measurable p hp
  have hq : Measurable 𝔠 𝔊 := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact 𝔙 𝔊
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := 𝔉)
    (Kernel.const 𝔊 (Measure.count : Measure 𝔍))
     fun _ _ => ENNReal.ofReal_ne_top
  rw [probability_pi_withDensity (cubeVolume d) _ hf hdesign n,
    responseSampleIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x : 𝔊 => ∏ i, ENNReal.ofReal (highNormalizedDensity p $ x i ))

      (Finset.measurable_prod _ fun i _ => hf.comp $ measurable_pi_apply i ) hq,
    Measure.compProd_const]
  congr 1
  funext z
  have hpn (i : Fin n) : 0 ≤ highNormalizedDensity p (z.1 i) :=
    div_nonneg 𝔡 hraw hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg 𝔔,
    ← ENNReal.ofReal_mul $ Finset.prod_nonneg 𝔔 ]
  simp [highSampleLikelihood, highNormalizedDensity]
