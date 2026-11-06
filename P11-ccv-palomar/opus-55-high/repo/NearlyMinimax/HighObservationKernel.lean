module

public import NearlyMinimax.HighObservationLaw
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Jointly measurable, normalized high-prior experiments over arbitrary raw states. -/
𝚴
𝛉
𝚨
𝚱
𝚩

𝛂

𝗇 𝔊 Ω → 𝙀
𝗃 𝔑 ἀ $ p ω
𝗃 𝔖 Measurable $ Function.uncurry ἀ
𝗇 𝔒 𝔖 p
theorem highRawDensityMass_joint_measurable (p : 𝔊)
    (hp : 𝔒) :
    Measurable fun ω => 𝔑 highRawDensityMass := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable

theorem ternaryMass_joint_measurable [MeasurableSpace α]
    a V F (hF : Measurable F) :
    Measurable fun z : α × Fin 3 => ternaryMass a (F z.1) V z.2 := measurable_from_prod_countable_left $ ternaryMass_measurable_comp a V F hF

𝗇 𝔄 𝙇 × 𝙈
𝗃 𝔗 (measurable_pi_apply i).comp $ ἀ measurable_snd
𝗃 𝔘 ἀ n a V
theorem highSampleLikelihood_joint_measurable (n : ℕ) (a V : ℝ)
    p F (hp : 𝔒)
    (hF : 𝔖 F) :
    Measurable fun z : Ω × 𝔄 =>
      𝔘 highSampleLikelihood (p z.1) (F z.1) z.2 := by
  have hx (i : Fin n) : Measurable
       fun z : Ω × 𝔄 => (z.1, z.2.1 i) :=
    measurable_fst.prodMk 𝔗 measurable_fst.comp
  have hy (i : Fin n) : Measurable
       fun z : Ω × 𝔄 => z.2.2 i :=
    𝔗 measurable_snd.comp
  exact ((Finset.measurable_prod _ fun i _ => hp.comp $ hx i ).div
    $ ((𝙨).comp measurable_fst).pow_const n ).mul
    $ Finset.measurable_prod _ fun i _ =>
      𝘍₁

/-- Fixed reference measure for the full design/finite-response experiment. -/
def highSampleReference (d n : ℕ) : Measure 𝔄 :=
  (Measure.pi 𝘂).prod Measure.count

𝗇 𝔓 𝘱
instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure 𝔓 := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference
  infer_instance

𝗇 𝔇 ENNReal.ofReal $ 𝔘 highSampleLikelihood (p ω) (F ω) z
𝗇 𝔔 fun ω z => 𝔇
/-- The joint sample kernel carries exactly the normalized raw likelihood. -/
def highSampleIndexKernel (n : ℕ) (a V : ℝ)
    (p F : 𝔊) (hp : 𝔒)
    (hF : 𝔖 F) :
    Kernel Ω 𝔄 := by
  let _ := cubeVolume_isProbability d
  exact (Kernel.const Ω 𝔓).withDensity
    𝔔

𝗇 𝔉 𝔘 highSampleIndexKernel p F hp hF
theorem highSampleIndexKernel_apply n a V
    p F hp
    hF (ω : Ω) :
    𝔉 ω =
      (𝔓).withDensity
         fun z => 𝔇 := by
  let _ := cubeVolume_isProbability d
  have hl : 𝔖 𝔔 :=
    ENNReal.measurable_ofReal.comp $ 𝔘 highSampleLikelihood_joint_measurable p F hp hF
  exact Kernel.withDensity_apply _ hl ω

𝗇 𝔅 highSample_index_density n (p ω) (F ω) hpω hFω a V hd (fun x => haRaw.le.trans (hraw ω x).1) hm $ hq ω
𝗇 𝔈 Filter.Eventually.of_forall $ hraw ω
𝗇 𝔍 ∀ ω x y, 0 ≤ 𝙅 V y
𝗇 𝔎 𝙄
𝗇 𝔏 haRaw.trans_le (𝔑 highRawDensityMass_mem_Icc hpω aRaw bRaw haRaw 𝔈).1
𝗇 𝔐 𝔑 normalizedDensityTernaryParameter_design_probability hpω aRaw bRaw haRaw 𝔈
/-- This family is a probability kernel on every raw state, including states
outside the original-model density interval after normalization. -/
theorem highSampleIndexKernel_markov n a V
    (p F : 𝔊) hp
    hF aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝔎) (ha : 𝙞)
    (hq : 𝔍) :
    IsMarkovKernel 𝔉 := by
  constructor
  intro ω
  have hpω : 𝔑 Measurable := hp.of_uncurry_left
  have hFω : Measurable $ F ω := hF.of_uncurry_left
  let hd := 𝔐
  let _ := hd
  let _ := 𝔘 responseSampleIndexKernel_markov (F ω) hFω ha $ hq ω
  have hm := 𝔏
  rw [highSampleIndexKernel_apply, highSampleReference]
  rw [← 𝔅]
  infer_instance

/-- Exact transfer of the normalized experiment to the original real-valued sample law. -/
theorem highSampleIndexKernel_encode n a V
    (p F : 𝔊) hp
    hF aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝔎) ha
    (hq : 𝔍) ω :
    (𝔉 ω).map (encodeDesignResponse a) =
      sampleLaw (𝔑 normalizedDensityTernaryParameter (F ω) a V
        hF.of_uncurry_left ha $ hq ω ) n := by
  have hpω : 𝔑 Measurable := hp.of_uncurry_left
  have hFω : Measurable $ F ω := hF.of_uncurry_left
  have hd := 𝔐
  have hm := 𝔏
  rw [highSampleIndexKernel_apply, highSampleReference]
  rw [← 𝔅]
  exact 𝔑 normalizedDensityTernaryParameter_sample_index_map hd n a V (F ω) hFω ha $ hq ω
