module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.HighUnionDensityCancellation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual canonical mass cancellation for the entire source packet,
including the singleton, all three pair rows, and every selected higher
coarse/fine row. Primitive cancellation is proved from finite response
atoms on the true carrier spaces. -/
𝚸
𝚪
𝚨
𝚩
𝛆
𝚬

𝗃 𝔜 ἀ d D M q
𝗃 𝔐 𝔜 ἀ a b
𝗃 𝔙 𝔐 ἀ C lam ℓ N μ
𝗇 𝔇 𝔙 SourceRowIndex
𝗇 𝔒 .inr $ .inl _
𝗇 𝔖 𝗱₁
𝗇 𝔗 𝚁
abbrev SourceRowDensityMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    𝔇 → Type
  | .inl p => FinePairRowDensityMark d D M p
  | 𝔒 => Unit × HighDensityMarkIndex D 1 D
  | 𝔖 => HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 ×
      HighDensityMarkIndex 𝔗 (higherBandFamilyTarget i.val) D

𝗇 𝔉 𝔙 SourceRowDensityMark i
instance sourceRowDensityMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔇) :
    MeasurableSpace 𝔉 := by
  cases i with
  | inl p => infer_instance
  | inr i => cases i <;> dsimp [SourceRowDensityMark] <;> infer_instance

𝗇 𝔊 𝔙 SourceRowMark i
𝗇 𝔔 fun e => 𝘆₂
def sourceRowDensityProj (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : 𝔇) →
      𝔊 → 𝔉
  | .inl p => 𝔜 finePairRowDensityProj p
  | 𝔒 => 𝔔
  | .inr $ .inr _ => 𝔔

𝗇 𝔍 fun e => (e.1,(e.2,r))
𝗇 𝔓 𝙮
def sourceRowDensityLift (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex 𝔓 q) :
    (i : 𝔇) →
      𝔉 → 𝔊
  | .inl p => 𝔜 finePairRowWithResponse p r
  | 𝔒 => 𝔍
  | .inr $ .inr _ => 𝔍

𝗇 𝔏 𝔙 sourceRowDensityLift r i
theorem sourceRowDensityLift_measurable d D M q a b C lam ℓ N μ
    r
    i :
    Measurable 𝔏 := by
  cases i with
  | inl p => exact 𝔜 finePairRowWithResponse_measurable p r
  | inr i => cases i <;> exact measurable_fst.prodMk $ measurable_snd.prodMk measurable_const

𝗃 𝔑 ἀ d k D M q a b
𝗇 𝔄 𝔑 sourceRowData C lam ℓ N μ
𝗇 𝔎 𝔙 sourceRowDensityProj i e
𝗇 𝔈 𝔏 𝔎
theorem sourceRow_density_projection_slope d k D M q a b C lam ℓ N μ
    r j
    i
    e x :
    (𝔄).rowSlope j i e x =
    (𝔄).rowSlope j i
      𝔈 x := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_projection_intercept d k D M q a b C lam ℓ N μ
    r
    i
    e :
    (𝔄).rowIntercept i e =
    (𝔄).rowIntercept i
      𝔈 := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

𝗇 𝔘 0 < (𝔄).rowMass i
theorem sourceRow_density_observable_zero (d : ℕ) [NeZero d] k D M q
    a b C lam ℓ N μ
    (hpos : ∀ i, 𝔘)
    i
    H (hH : Measurable H)
    B (hB : ∀ z, ‖H z‖ ≤ B) :
     ∫ e, (𝔄).rowActivation i e *
      H 𝔎
      ∂(𝔄).rowLaw i = 0 := by
  cases i with
  | inl p =>
    exact 𝔐 finePairRow_density_observable_zero C ℓ N
      (fun p => hpos $ Sum.inl p ) p H hH B hB
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketAbsoluteLaw_density_observable_zero 𝖶₁ a b D 1 D q C
        𝗻 𝗱 (integrable_const _)
        (hpos 𝘊₁) H hH B hB
    | inr i =>
      exact higherBandRow_density_observable_zero d (higherBandFamilyTarget i.val)
        𝔗 D q a b C lam ℓ
        𝙽 i.val.2 i.property.1
        (hpos 𝔖) H hH B hB

theorem sourceRowMass_positive_actual (d : ℕ) [NeZero d] k D M q
    (hD : 𝗕) (hq : 𝗘) a b (ha : 𝙆) (hab : 𝙭)
    C (hC : 𝙴) lam ℓ N μ (hℓ : 𝙲₁) (hℓN : 𝖰₂)
    i :
    𝔘 := by
  cases i with
  | inl p => exact 𝙿₁ C hC ℓ N hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => exact 𝘇₂ C hC
    | inr i => exact 𝔑 higherBandFamily_mass_positive C lam ℓ N μ i

𝗇 𝔅 𝖻 lam ℓ N μ
𝗃 𝔚 𝔐 ἀ Cfr lam ℓ N μ
𝗃 𝔛 𝔑 ἀ Cfr lam ℓ N μ r₀
/-- Genuine canonical append annihilation for the complete actual source
family, with only the original construction's numerical guards. -/
theorem completeSourceMass_append_indicator_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder 𝙯]
    C (hD : 𝗕) (hq : 𝗘)
    (hM : 𝘧)
    Cfr lam ℓ N μ (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂)
    j
    h S (hS : MeasurableSet S) :
     ∫ e, S.indicator 𝘋₁
      (highUnionSourceMass C 𝔅
        $ historyMarkedAppend 𝖫
          𝗘₁ j 𝖷₁ ) *
      highUnionActivation 𝔅 (highCenterMix C) e
      ∂highUnionLaw 𝔅 (highCenterMix C) = 0 := by
  let a := C.densityLower+𝗙
  let b := C.densityUpper-𝗙
  let R := 𝔅
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr  𝖡₄  lam ℓ N μ hℓ hℓN
  let β₀ : 𝔓 := ⟨𝖾,𝖢₄⟩
  let r₀ : HighResponseMarkIndex 𝔓 q := 𝖵₁
  exact highUnionSourceMass_append_indicator_zero_of_density_projection C R
    (𝖠 ℓ N μ hCfr hℓ hℓN) hpos
    𝔚 SourceRowDensityMark
    𝔚 sourceRowDensityProj
    (𝔚 sourceRowDensityLift r₀)
    (𝔚 sourceRowDensityLift_measurable r₀)
    𝔛 sourceRow_density_projection_slope
    𝔛 sourceRow_density_projection_intercept
    (𝔑 sourceRow_density_observable_zero Cfr lam ℓ N μ hpos) j h S hS
