module

public import NearlyMinimax.HighObservationReal
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine positive mass-power prior tilts and normalization cancellation. -/
𝚴
𝚮
𝚨
𝚱
𝚩
𝛂

𝗇 𝔜 m ω ^ n
def massPowerNormalizer (μ : Measure Ω) (m : 𝘄) (n : ℕ) : ℝ :=
  ∫ ω, 𝔜 ∂μ

𝗇 𝔍 massPowerNormalizer μ m n
def massPowerTilt (μ : Measure Ω) (m : 𝘄) (n : ℕ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal $ 𝔜 / 𝔍

𝗇 𝔇 ∀ ω, a ≤ m ω ∧ m ω ≤ b
𝗃 𝔢 (hbound ἀ).1
𝗇 𝔈 ha.le.trans 𝔢 ω
𝗇 𝔒 b ^ n
𝗇 𝔛 pow_le_pow_left₀ 𝔈 (hbound ω).2 n
𝗇 𝔞 𝙆
𝗇 𝔟 pow_nonneg 𝔈 n
theorem massPower_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n (a b : ℝ) (ha : 𝔞)
    (hbound : 𝔇) : Integrable (fun ω => 𝔜) μ := by
  apply (integrable_const 𝔒).mono' (hm.pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg 𝔟]
  exact 𝔛

𝗃 𝔗 ἀ μ m hm n a b ha hbound
𝗇 𝔠 a ^ n
theorem massPowerNormalizer_mem_Icc (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n a b (ha : 𝔞)
    (hbound : 𝔇) :
    𝔍 ∈ Icc 𝔠 𝔒 := by
  have hi := 𝔗 massPower_integrable
  constructor
  · simpa [massPowerNormalizer] using integral_mono_ae (integrable_const 𝔠) hi
      $ Filter.Eventually.of_forall fun ω => pow_le_pow_left₀ ha.le 𝔢 ω n
  · simpa [massPowerNormalizer] using integral_mono_ae hi (integrable_const 𝔒)
      $ Filter.Eventually.of_forall fun ω =>
        𝔛

theorem massPowerNormalizer_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n a b (ha : 𝔞)
    (hbound : 𝔇) : 0 < 𝔍 :=
  (pow_pos ha n).trans_le (𝔗 massPowerNormalizer_mem_Icc).1

theorem massPowerTilt_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n a b (ha : 𝔞)
    (hbound : 𝔇) : IsProbabilityMeasure $ massPowerTilt μ m n := by
  have hi := 𝔗 massPower_integrable
  have hG := 𝔗 massPowerNormalizer_pos
  constructor
  rw [massPowerTilt, 𝚒₂]
  simp
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
    $ Filter.Eventually.of_forall fun ω =>
      div_nonneg 𝔟 hG.le , integral_div]
  change ENNReal.ofReal (𝔍 / 𝔍) = 1
  aesop

𝗇 𝔔 𝖡₁
𝗇 𝔙 (measurable_id.pow_const n).stronglyMeasurable
/-- Equality of actual mass laws makes the power normalizer time independent. -/
theorem massPowerNormalizer_eq_of_massLaw (μ ν : Measure Ω) m
    (hm : Measurable m) n (hlaw : μ.map m = ν.map m) :
    𝔍 = 𝔔 := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    𝔙
  have hν := integral_map_of_stronglyMeasurable (μ := ν) hm
    𝔙
  aesop

𝗃 𝔥 fun ω => ἀ $ m ω
𝗇 𝔐 𝔥 f
/-- Pushing a pullback density forward gives the density of the pushed-forward law. -/
theorem map_withDensity_pullback [MeasurableSpace Α]
    (μ : Measure Ω) (m : Ω → Α) (hm : Measurable m)
    f (hf : Measurable f) :
    (μ.withDensity 𝔐).map m = (μ.map m).withDensity f := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hfm : Measurable 𝔐 := hf.comp hm
  have hGm : Measurable 𝔥 G := hG.comp hm
  rw [lintegral_map hG hm,
    lintegral_withDensity_eq_lintegral_mul _ hfm hGm,
    lintegral_withDensity_eq_lintegral_mul _ hf hG,
    lintegral_map (hf.mul hG) hm]
  rfl

𝗃 𝔦 (ἀ n).div_const _
/-- The tilted mass law, hence its exceptional mass probabilities, depends
only on the original mass law. -/
theorem massPowerTilt_massLaw_eq (μ ν : Measure Ω) m
    (hm : Measurable m) n (hlaw : μ.map m = ν.map m) :
    (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
  unfold massPowerTilt
  rw [ massPowerNormalizer_eq_of_massLaw μ ν m hm n hlaw ]
  have hf : Measurable fun x => ENNReal.ofReal $ x ^ n / 𝔔 :=
    ENNReal.measurable_ofReal.comp 𝔦 measurable_id.pow_const
  rw [map_withDensity_pullback μ m hm _ hf, map_withDensity_pullback ν m hm _ hf, hlaw]

𝗇 𝔄 𝙇 × 𝙈
𝗇 𝔖 𝙀
/-- The unnormalized product likelihood appearing in the weak generator. -/
def highRawSampleLikelihood (n : ℕ) (a V : ℝ)
    (p F : 𝔖) (z : 𝔄) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F $ z.1 i ) V (z.2 i)

𝗃 𝔘 ἀ n a V (p z.1) $ F z.1
𝗇 𝔎 𝔘 highRawSampleLikelihood z.2
𝗃 𝔣 Measurable $ Function.uncurry ἀ
𝗃 𝔤 (measurable_pi_apply i).comp $ ἀ measurable_snd
theorem highRawSampleLikelihood_joint_measurable (n : ℕ) (a V : ℝ)
    p F (hp : 𝔣 p)
    (hF : 𝔣 F) :
    Measurable fun z : Ω × 𝔄 =>
      𝔎 := by
  have hx (i : Fin n) : Measurable
       fun z : Ω × 𝔄 => (z.1, z.2.1 i) :=
    measurable_fst.prodMk 𝔤 measurable_fst.comp
  have hy (i : Fin n) : Measurable
       fun z : Ω × 𝔄 => z.2.2 i :=
    𝔤 measurable_snd.comp
  exact Finset.measurable_prod _ fun i _ => (hp.comp $ hx i ).mul
    𝘍₁

𝗃 𝔡 ἀ n a V p F
theorem highSampleLikelihood_mass_cancellation n a V
    (p F : 𝔖) (hm : highRawDensityMass p ≠ 0)
    z :
    highRawDensityMass p ^ n * 𝔡 highSampleLikelihood z =
      𝔡 highRawSampleLikelihood z := by
  simp only [highSampleLikelihood, highRawSampleLikelihood, Finset.prod_mul_distrib]
  field_simp

𝗇 𝔑 𝔡 highSampleIndexKernel hp hF
𝗇 𝔚 fun _ _ => ENNReal.ofReal_ne_top
instance highSampleIndexKernel_isSFinite (n : ℕ) (a V : ℝ)
    (p F : Ω → 𝔖) (hp : 𝔣 p)
    (hF : 𝔣 F) : IsSFiniteKernel 𝔑 := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ 𝔚

𝗇 𝔅 fun ω z => ENNReal.ofReal $ highSampleLikelihood n a V (p ω) (F ω) z
𝗇 𝔉 𝙙
𝗇 𝔊 fun ω => ENNReal.ofReal $ m ω ^ n / 𝖡₁
𝗇 𝔏 𝔘 highSampleLikelihood z.2
𝗇 𝔓 𝘱
/-- The actual tilted-prior/sample measure has the raw product likelihood
 divided only by the prior normalizer. -/
theorem massPowerTilt_highSample_compProd (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → 𝔖)
    hp hF
    aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝙄) :
    (massPowerTilt ν 𝔉 n).compProd
      𝔑 =
      (ν.prod 𝔓).withDensity fun z =>
        ENNReal.ofReal $ 𝔎 /
          massPowerNormalizer ν 𝔉 n := by
  let m := 𝔉
  have hm := 𝙨
  have hbound ω :=
    𝖤₁
  have hG := 𝘰₁ hbound
  have hd : Measurable 𝔊 :=
    ENNReal.measurable_ofReal.comp 𝔦 hm.pow_const
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := 𝔅)
    (Kernel.const Ω 𝔓) 𝔚
  change (ν.withDensity 𝔊).compProd
    ((Kernel.const Ω 𝔓).withDensity
      𝔅) = _
  rw [Measure.withDensity_compProd_withDensity

    (g := 𝔅) hd $ ENNReal.measurable_ofReal.comp $ 𝔡 highSampleLikelihood_joint_measurable hp hF ,
    Measure.compProd_const]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul $ div_nonneg (pow_nonneg (haRaw.le.trans 𝔢 z.1) n) hG.le ]
  congr 1
  calc
     m z.1 ^ n / 𝔔 * 𝔏 =
         m z.1 ^ n * 𝔏 / 𝔔 := 𝖢₃
    𝘿 := by rw [𝔘 highSampleLikelihood_mass_cancellation
      (haRaw.trans_le 𝔢 z.1).ne']
