module

public import NearlyMinimax.FinePairRows
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Primitive Borel, interval and reference-centering facts for the actual
three-row fine-pair data. -/
𝚫
𝚨

𝗇 𝔞 𝙮
𝗇 𝔄 HighPacketMarkIndex 𝔞 D 2 D q
𝗇 𝔚 (Z × 𝔄) × Covariate d
𝗃 𝔮 ἀ a b
𝗃 𝔣 𝔮 ἀ D 2 D
𝗇 𝔠 𝔣 densityPacketAtom
𝗇 𝔪 2 * b
𝗃 𝔴 𝔮 densityMargin (𝔠 ἀ).1 / 𝔪
theorem highPacketSlope_joint_measurable_finePair [MeasurableSpace Z]
    (d D q : ℕ) (a b : ℝ) (B : Z → Covariate d → 𝖷₂)
    (hB : 𝗠₂) :
    Measurable fun ex : 𝔚 =>
      𝔣 highPacketSlope q (fun ζ l => B ζ ex.2 l) ex.1 := by
  have hc : Measurable fun ex : 𝔚 =>
      𝔴 ex.1.2.1 :=
    (measurable_of_countable fun h : 𝔄 =>
      𝔴 h.1 ).comp
        $ measurable_snd.comp measurable_fst
  have he (l : Fin 2) : Measurable fun ex : 𝔚 =>
      (𝔠 ex.1.2.1).2 l :=
    (measurable_of_countable fun h : 𝔄 =>
      (𝔠 h.1).2 l ).comp $ measurable_snd.comp measurable_fst
  exact hc.mul 𝚜

𝗃 𝔯 ἀ d D M q
𝗇 𝔢 𝔯 finePairRowIntercept a b i
theorem finePairRowIntercept_measurable d D M q a b i :
    Measurable 𝔢 := by
  cases i
  · exact 𝔣 highPacketIntercept_measurable q
  · exact 𝔣 highPacketIntercept_measurable q
  · exact 𝔮 finePairPacketIntercept_measurable M q

𝗇 𝔐 (highResponseMarkAtom C q h.2).2 γ
𝗃 𝔱 (measurable_of_countable fun h : 𝔄 => ἀ ).comp measurable_snd
𝗇 𝔛 𝔱 𝔐
𝗃 𝔬 (measurable_of_countable fun h : FinePairPacketIndex 𝔞 M q => ἀ ).comp measurable_snd
theorem finePairRowVector_measurable d D M q C i
    γ : Measurable fun e => 𝔯 finePairRowVector C i e γ := by
  cases i
  · exact 𝔛
  · exact 𝔛
  · exact 𝔬 𝔐

𝗇 𝔓 (highResponseMarkAtom 0 q h.2).1
𝗇 𝔜 𝔱 𝔓
theorem finePairRowTime_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    Measurable $ 𝔯 finePairRowTime i := by
  cases i
  · exact 𝔜
  · exact 𝔜
  · exact 𝔬 𝔓

𝗇 𝔅 𝗂₂
𝗇 𝔘 fun _ => 𝙃
𝗃 𝔦 ἀ d k D M q a b
𝗃 𝔨 fun _ => ἀ
𝗇 𝔫 finePairTimeFieldValue ζ 𝔅
theorem finePairRowSlope_joint_measurable d k D M q a b
    j i :
    Measurable fun ex : 𝔯 FinePairRowMark i × Covariate d =>
      𝔦 finePairRowSlope j i ex.1 ex.2 := by
  have hψ :=
    (finePairTimeFieldValue_measurable d).comp
      $ measurable_fst.prodMk $ (highLocalCoordinates_measurable d k j).comp measurable_snd
  cases i
  · exact (𝔣 highPacketSlope_measurable q 𝔘
      𝔨 measurable_const).comp measurable_fst
  · exact highPacketSlope_joint_measurable_finePair d D q a b
      (fun ζ x _ => 𝔫) 𝔨 hψ
  · exact 𝔮 finePairPacketSlope_joint_measurable M q
      (fun ζ x => 𝔫) hψ

𝗇 𝔈 𝔦 finePairRowSlope j i e x
𝗇 𝔊 𝔮 densityPacketAtom_mem hab.le D 2 D e.2.1
𝗇 𝔎 𝔣 densityPacketAtom e.2.1
𝗇 𝔔 𝔨 v
𝗃 𝔰 (finePairTimeFieldValue_abs ἀ _).le
theorem finePairRow_reset_interval d k D M q a b (ha : 𝙆) (hab : 𝙭)
    j i e
    x v (hv : v ∈ 𝔮 Icc) :
    𝔈 * v + 𝔢 e ∈ 𝔮 Icc := by
  cases i
  · have h := 𝔮 localDensityReset_mem_interval ha hab 2  𝖠₄ 
      (𝔎).1 (𝔊).1
      (𝔎).2 (𝔊).2
      𝔔 𝘞 () hv 𝖢₄
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := 𝔮 localDensityReset_mem_interval ha hab 2  𝖠₄ 
      (𝔎).1 (𝔊).1
      (𝔎).2 (𝔊).2
      𝔔 (fun _ _ => finePairTimeFieldValue e.1 𝔅)
      () hv fun _ => 𝔰 e.1
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := 𝔮 finePairDensityReset_mem_interval ha hab _ _
      (𝔮 finePairPacketIntercept_mem hab.le M q e) (fineModulationNode_bound e.2.1.2)
      𝔔 (fun _ => finePairTimeFieldValue e.1 𝔅) () hv
      𝔰 e.1
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
      finePairDensityReset, finePairDensityAtom] <;> ring

section Reference
𝗃 𝔤 𝔯 ἀ a b C T₀ N
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < 𝔤 finePairRowMass i)
include hpos

𝗇 𝔇 𝔤 finePairRowLaw i
𝗇 𝔉 𝖼₂
𝗇 𝔍 𝗱
𝗇 𝔏 𝗻
𝗇 𝔑 finePairTimeMatrix_cost_integrable d 0 T₀ _
𝗇 𝔒 finePairTimeMatrix_cost_integrable d T₀ N _
𝗇 𝔖 finePairTimeFieldMeasure d 0 T₀
𝗇 𝔗 finePairTimeFieldMeasure d T₀ N
𝗇 𝔙 𝖶₁
𝗃 𝔥 ἀ 𝔗 a b M q C _ 𝔉 𝔒 $ hpos .fine
𝗃 𝔧 ἀ 𝔙 a b D 2 D q C 𝔏 𝔍 (integrable_const _) $ hpos .unit
𝗃 𝔭 ἀ 𝔖 a b D 2 D q C _ 𝔉 𝔑 $ hpos .coarse
theorem finePairRowLaw_probability i :
    IsProbabilityMeasure 𝔇 := by
  cases i
  · exact 𝔧 highPacketAbsoluteLaw_probability
  · exact 𝔭 highPacketAbsoluteLaw_probability
  · exact 𝔥 finePairPacketAbsoluteLaw_probability

𝗇 𝔡 𝔤 finePairRowActivation i
𝗃 𝔲 absoluteActivation_measurable _ _ $ 𝔣 highPacketMarkWeight_measurable q C _ ἀ
theorem finePairRowActivation_measurable i :
    Measurable 𝔡 := by
  cases i
  · exact 𝔲 𝔍
  · exact 𝔲 𝔉
  · exact absoluteActivation_measurable _ _ $ 𝔮 finePairPacketWeight_measurable M q C _
      𝔉

theorem finePairRowActivation_centered i :
     ∫ e, 𝔡 e ∂𝔇 = 0 := by
  cases i
  · exact 𝔧 highPacketActivation_centered
  · exact 𝔭 highPacketActivation_centered
  · exact 𝔥 finePairPacketActivation_centered

𝗇 𝔩 fun e => 𝔈
theorem finePairRowSlope_integrable (ha : 𝙆) (hab : 𝙭)
    j x i :
    Integrable 𝔩
      𝔇 := by
  letI := 𝔤 finePairRowLaw_probability hpos i
  have hm : Measurable 𝔩 :=
    (𝔦 finePairRowSlope_joint_measurable j i).comp
    $ measurable_id.prodMk measurable_const
  apply (integrable_const $ 𝘅/𝖾₂ ).mono' hm.aestronglyMeasurable
  filter_upwards [] with e
  simpa only [Real.norm_eq_abs] using 𝔦 finePairRowSlope_bound ha hab j i e x

𝗇 𝔟 fun ζ => 𝔫
𝗃 𝔳 highPacketAbsoluteLaw_slope_integral_zero ἀ a b ha hab D 2 D q
theorem finePairRowSlope_centered (ha : 𝙆) (hab : 𝙭)
    j x i :
     ∫ e, 𝔈 ∂𝔇 = 0 := by
  have hm : Measurable 𝔟 :=
    (boundedHyperplaneFieldValue_section_measurable d _).comp measurable_snd
  cases i
  · exact 𝔳 𝔙  𝖠₄ 
      C 𝔏 𝔍 (integrable_const _) (hpos .unit)
      𝔘 𝔨 measurable_const 𝖢₄
  · exact 𝔳 𝔖  𝖠₄  C _ 𝔉
      𝔑 (hpos .coarse)
      (fun ζ _ => 𝔫) 𝔨 hm
       fun ζ _ => 𝔰 ζ
  · exact 𝔥 finePairPacketAbsoluteLaw_slope_integral_zero
      ha hab 𝔟 hm
       fun ζ => 𝔰 ζ
