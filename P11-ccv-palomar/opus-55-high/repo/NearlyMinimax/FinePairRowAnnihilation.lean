module

public import NearlyMinimax.FinePairRows
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Every bounded Borel density observable is killed by the genuine
uncentered response packet, under its actual absolute reference law. -/
𝚫
𝚪
𝚨
𝚩
𝚱

theorem finite_response_density_zero [Fintype I] [Fintype J]
    (w : 𝗦₂) (v : 𝙝) (hv : ∑ j, v j = 0) (F : 𝗦₂) :
     ∑ h : I × J, w h.1 * v h.2 * F h.1 = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  have he j : w i * v j * F i = w i * F i * v j := 𝖢₃
  simp only [he, ← Finset.mul_sum, hv, mul_zero]

section Generic
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔄 highResponseMark_action q C (A ζ) 𝖾 𝙃
𝗇 𝔅 𝗨₂ $ A ζ
𝗇 𝔇 𝘆₂
𝗇 𝔈 𝙚
𝗇 𝔉 𝚊
𝗇 𝔊 ∑ h : 𝗧₂, 𝔅 h = 0
𝗇 𝔍 Filter.Eventually.of_forall fun e => hbound 𝔇
section

variable (σ : Measure Z)
    [IsFiniteMeasure σ]
    (a)
    (b)

𝗃 𝔎 ἀ σ a b m r D q C A
𝗇 𝔐 𝘛₂
𝗇 𝔑 measurable_fst.prodMk $ measurable_fst.comp measurable_snd
𝗇 𝔒 fun h => F 𝔉
𝗇 𝔓 Z → ι → 𝙛
𝗃 𝔔 ἀ a b m r D
theorem highPacketAbsoluteLaw_density_observable_zero m r D q C (A : 𝔓)
    (hA : 𝔈) (hcost : 𝙧)
    (hpos : 0 < 𝔎 highPacketMarkMass)
    F (hF : Measurable F)
    L (hbound : 𝔐) :
     ∫ e, 𝔎 highPacketActivation e * F 𝔇
      ∂𝔎 highPacketAbsoluteLaw = 0 := by
  have hm : Measurable fun e : Z × 𝘷₁ => F 𝔇 :=
    hF.comp 𝔑
  have hi := (𝔎 highPacketMarkWeight_integrable hA hcost).mul_bdd hm.aestronglyMeasurable
    𝔍
  rw [highPacketActivation, highPacketAbsoluteLaw, absoluteMarkLaw_activation_integral _ _
    (𝔔 highPacketMarkWeight_measurable q C A hA) hpos,
    integral_prod _ hi]
  have he ζ : ∑ h : 𝘷₁,
      𝔔 highPacketMarkWeight q C A 𝔉 * F (ζ,h.1) = 0 := by
    have hz : 𝔊 := by
      simpa only [mul_one, responseMatrixAction_zero_mass] using 𝔄
    exact finite_response_density_zero 𝔔 densityPacketWeight
      𝔅 hz 𝔒
  simp_all

𝗃 𝔏 ἀ σ a b M q C A
theorem finePairPacketAbsoluteLaw_density_observable_zero M q C (A : 𝔓)
    (hA : 𝔈) (hcost : 𝙧)
    (hpos : 0 < 𝔏 finePairPacketMarkMass)
    F (hF : Measurable F)
    L (hbound : 𝔐) :
     ∫ e, 𝔏 finePairPacketActivation e * F 𝔇
      ∂𝔏 finePairPacketAbsoluteLaw = 0 := by
  have hm : Measurable fun e : Z × FinePairPacketIndex ι M q => F 𝔇 :=
    hF.comp 𝔑
  have hi := (𝔏 finePairPacketWeight_integrable hA hcost).mul_bdd hm.aestronglyMeasurable
    𝔍
  rw [finePairPacketActivation, finePairPacketAbsoluteLaw, absoluteMarkLaw_activation_integral _ _
    (finePairPacketWeight_measurable a b M q C A hA) hpos,
    integral_prod _ hi]
  have he ζ : ∑ h : FinePairPacketIndex ι M q,
      finePairPacketWeight a b M q C A 𝔉 * F (ζ,h.1) = 0 := by
    have hz : 𝔊 := by
      simpa only [mul_one, responseMatrixAction_zero_mass] using 𝔄
    exact finite_response_density_zero (finePairDensityWeight a b M)
      𝔅 hz 𝔒
  simp_all
