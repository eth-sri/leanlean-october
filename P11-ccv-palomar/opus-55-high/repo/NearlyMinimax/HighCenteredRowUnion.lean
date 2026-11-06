module

public import NearlyMinimax.HighRowReferenceUnion
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The paper's global tagged Xi reference construction: first mix the
absolute row laws with their true variation masses, then add exactly one
zero-weight corrective branch. The generator action and source activation
constant are preserved by actual positive-measure integral identities. -/
𝚫
𝚪
𝚨
𝚩
𝚰
𝚬

section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace $ E j ]

𝗇 𝔇 (j : J) → Measure $ E j
𝗇 𝔉 Sigma E ⊕ Unit
𝗇 𝔐 highRowReferenceUnion π B
def highCenteredRowUnionLaw (π : 𝔇) (B : 𝙝) (δ : ℝ) :
    Measure 𝔉 := balancedReferenceLaw 𝔐 δ

𝗇 𝔅 (j : J) → E j → ℝ
def highCenteredRowUnionActivation (B : 𝙝) (w : 𝔅) (δ : ℝ) :
    𝔉 → ℝ := balancedActivation (highRowUnionActivation B w) δ

𝗃 𝔞 fun e : Sigma E => ἀ e.1 e.2
def highCenteredRowUnionIntercept (π : 𝔇) (B : 𝙝)
    (intercept : 𝔅) (δ : ℝ) : 𝔉 → ℝ :=
  balancedIntercept 𝔞 intercept δ
    $ ∫ e : Sigma E, intercept e.1 e.2 ∂𝔐

def highCenteredRowUnionSlope (slope : 𝔅) : 𝔉 → ℝ :=
  balancedSlope 𝔞 slope

𝗇 𝔈 ∀ j, 0 ≤ B j
𝗇 𝔊 ∀ j, IsProbabilityMeasure $ π j
𝗇 𝔎 0 < highRowTotalMass B
𝗇 𝔑 highCenteredRowUnionLaw π B δ
𝗇 𝔗 highRowReferenceUnion_probability π B hB hTotal
theorem highCenteredRowUnionLaw_probability (π : 𝔇)
    [𝔊] B (hB : 𝔈)
    (hTotal : 𝔎) δ (hδ0 : 𝚈) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure 𝔑 := by
  letI := 𝔗
  exact balancedReferenceLaw_probability _ δ hδ0 hδ1

𝗃 𝔔 ∀ j, Measurable $ ἀ j
𝗇 𝔘 highCenteredRowUnionActivation B w δ
𝗇 𝔚 highRowUnionActivation_measurable B w hw
𝗃 𝔖 ∀ j, ∫ e, ἀ j e ∂π j = 0
𝗃 𝔠 ∀ j, Integrable (ἀ j) $ π j
theorem highCenteredRowUnionActivation_centered π
    B (hB : 𝔈) (w : 𝔅)
    (hw : 𝔔 w) (hInt : 𝔠 w)
    (hCenter : 𝔖 w)
    δ (hδ : 𝙮₂) (hδ1 : δ ≤ 1) :
     ∫ e, 𝔘 e ∂𝔑 = 0 :=
  balancedActivation_integral_zero _ δ hδ hδ1 _ 𝔚
    (highRowUnionActivation_integrable π B w hw hInt)
    $ highRowUnionActivation_centered π B hB w hw hInt hCenter

theorem highCenteredRowUnionActivation_bound B (hB : ∀ j, 0 < B j)
    (hTotal : 𝔎) w
    (hw : ∀ j e, |w j e| ≤ B j) δ (hδ : 𝙮₂) (e : 𝔉) :
    |𝔘 e| ≤ highRowTotalMass B / δ := by
  apply balancedActivation_bound _ δ _ hδ hTotal.le
  intro e
  simpa only [div_one] using highRowUnionActivation_bound B hB hTotal 1  𝖠₄ 
    w  𝖧₄  e

theorem highCenteredRowUnionActivation_measurable B
    (w : 𝔅) (hw : 𝔔 w) δ :
    Measurable 𝔘 :=
  balancedActivation_measurable _ 𝔚 δ

𝗇 𝔒 rowSigmaFunction_measurable slope hSlope
theorem highCenteredRowUnionSlope_measurable (slope : 𝔅)
    (hSlope : 𝔔 slope) : Measurable $ highCenteredRowUnionSlope slope :=
  balancedSlope_measurable _ 𝔒

𝗇 𝔍 𝔔 intercept
𝗇 𝔏 rowSigmaFunction_measurable intercept hIntercept
theorem highCenteredRowUnionIntercept_measurable π B
    (intercept : 𝔅) (hIntercept : 𝔍) δ :
    Measurable $ highCenteredRowUnionIntercept π B intercept δ :=
  balancedIntercept_measurable _ 𝔏 δ _

theorem highCenteredRowUnionSlope_integral_zero π
    B (hB : 𝔈) (hTotal : 𝔎)
    (slope : 𝔅) (hSlope : 𝔔 slope)
    (hiSlope : 𝔠 slope)
    (hCenter : 𝔖 slope)
    δ (hδ0 : 𝚈) (hδ1 : δ ≤ 1) :
     ∫ e, highCenteredRowUnionSlope slope e ∂𝔑 = 0 :=
  balancedSlope_integral_zero _ δ hδ0 hδ1 _ 𝔒
    (highRowReferenceUnion_integrable π B _ 𝔒 hiSlope)
    $ highRowReferenceUnion_integral_common_mean π B hB hTotal slope hSlope hiSlope 0 hCenter

𝗇 𝔓 fun e => hBound e.1 e.2
𝗃 𝔡 ∀ j e, intercept j e ∈ ἀ
theorem highCenteredRowUnionIntercept_integral_one (π : 𝔇)
    [𝔊] B (hB : 𝔈)
    (hTotal : 𝔎)
    intercept (hIntercept : 𝔍)
    a b (hBound : 𝔡 𝘔₂)
    δ (hδ0 : 𝚈) (hδ1 : δ < 1) :
     ∫ e, highCenteredRowUnionIntercept π B intercept δ e ∂𝔑 = 1 := by
  letI := 𝔗
  exact balancedIntercept_integral_one _ δ hδ0 hδ1 _
    𝔏
    $ boundedIntercept_integrable 𝔐 _
      𝔏 a b 𝔓

𝗇 𝔛 C.densityLower+𝗙
𝗇 𝔜 C.densityUpper-𝗙
𝗇 𝔄 Icc 𝔛 𝔜
𝗇 𝔙 𝔡 𝔄
/-- The source's single corrective intercept is legal at its uniform
resolution threshold, for the actual total union intercept mean. -/
theorem highCenteredRowUnionIntercept_source_interval (C : ModelConstants d)
    (π : 𝔇) [𝔊]
    B (hB : 𝔈) (hTotal : 𝔎)
    intercept (hIntercept : 𝔍)
    M (hM : 𝘧)
    (hBound : 𝔙) :
    ∀ e, highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      𝔄 := by
  letI := 𝔗
  have hg := 𝚀₁ hM
  have hq := boundedIntercept_mean_mem 𝔐
    (fun e => intercept e.1 e.2) 𝔏
    𝔛 𝔜 𝔓
  intro e
  cases e with
  | inl e => exact hBound e.1 e.2
  | inr u =>
    exact sourceBalancedResetAnchor_mem C M _  𝖡₄  hg.2 hq

/-- Source global density reset legality, including the one corrective branch. -/
theorem highCenteredRowUnion_reset_source_legal (C : ModelConstants d)
    (π : 𝔇) [𝔊]
    B (hB : 𝔈) (hTotal : 𝔎)
    slope intercept (hIntercept : 𝔍)
    M (hM : 𝘧)
    (hBound : 𝔙)
    (hlegal : ∀ j e p, p ∈ 𝔄 →
      slope j e*p+intercept j e ∈ 𝔄)
    e p
    (hp : p ∈ 𝔄) :
    highCenteredRowUnionSlope slope e*p+highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      𝔄 := by
  cases e with
  | inl e => exact hlegal e.1 e.2 p hp
  | inr u =>
    simpa only [highCenteredRowUnionSlope, balancedSlope, Sum.elim_inr, zero_mul, zero_add]
      using highCenteredRowUnionIntercept_source_interval C π B hB hTotal intercept hIntercept
        M hM hBound $ Sum.inr u
