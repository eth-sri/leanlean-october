module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionScorePrimitives
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual response-coordinate elimination makes every appended density
product annihilate under the full source activation, at every sample count. -/
𝚫
𝚪
𝚨
𝛆
𝛀
𝚬
𝚿

 set_option hygiene false
𝗇 𝔅 lift i $ project i e
𝗇 𝔑 𝘖₁
𝗇 𝔇 𝔑 e $ x i
𝗇 𝔈 𝗋₁
𝗇 𝔉 project i e
𝗇 𝔎 C.densityUpper^n
𝗇 𝔏 𝙯
𝗇 𝔐 R.rowSlope j i
𝗃 𝔒 ∫ e, R.rowActivation i e * ἀ 𝔉 ∂ R.rowLaw i
theorem highUnionSourceResetDensity_product_zero_of_density_projection
    [NeZero k] [LinearOrder 𝔏]
    [Fintype I] [𝙪]
    [𝖭] (C : ModelConstants d)
    (R : 𝗽) (G : 𝗗)
    (hpos : 𝚣)
    (D : 𝗀) [∀ i, MeasurableSpace $ D i ]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable $ lift i )
    (hSlope : ∀ j i e x, 𝔐 e x = 𝔐 𝔅 x)
    (hIntercept : ∀ i e, 𝘅₂ = R.rowIntercept i 𝔅)
    (hRowZero : ∀ i, ∀ H , Measurable H → ∀ L ,
      (∀ z, ‖H z‖ ≤ L) → 𝔒 H = 0)
    j
    h
    n (x : 𝙇) :
     ∫ e, 𝗾 e *
      ∏ i, 𝔇 ∂𝗛 = 0 := by
  let Fobs := fun e => ∏ i, 𝔇
  have hF : Measurable Fobs := Finset.measurable_fun_prod _ fun i _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp $ measurable_id.prodMk measurable_const
  have hFb e : ‖Fobs e‖ ≤ 𝔎 := by
    simpa only [Real.norm_eq_abs,Fobs] using finite_density_product_abs_bound
      (fun i => 𝔇) C.densityUpper
      (by linarith [C.one_lt_densityUpper])
       fun i => highUnionSourceResetDensity_abs_le C R G j h e $ x i
  have hp i e z :
      𝔑 𝔈 z =
      𝔑 (Sum.inl ⟨i,𝔅⟩) z := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if z ∈ 𝘋 then 𝔐 e z * _ + 𝘅₂ else _) =
       if z ∈ 𝘋 then 𝔐 𝔅 z * _ +
        R.rowIntercept i 𝔅 else _
    grind
  have hrow i : ∫ e, R.rowActivation i e * Fobs 𝔈 ∂ R.rowLaw i = 0 := by
    let Hi := fun z => Fobs $ Sum.inl ⟨i,lift i z⟩
    have hHi := hF.comp
      𝙳₂
    have he e : Fobs 𝔈 = Hi 𝔉 := by
      grind
    calc
      _ = 𝔒 Hi :=
        integral_congr_ae $ Filter.Eventually.of_forall fun e => congrArg _ $ he e
      _ = 0 := hRowZero i Hi hHi 𝔎 fun z => hFb _
  rw [highUnionSource_bounded_action C R G hpos Fobs hF 𝔎 hFb]
  simp_all

𝗇 𝔄 𝖻 lam ℓ N μ
𝗃 𝔊 ἀ d D M q a b Cfr lam ℓ N μ
𝗃 𝔍 ἀ d k D M q a b Cfr lam ℓ N μ
/-- Complete actual singleton, pair, and higher coarse/fine rows have
conditional density-product zero mass at every count. -/
theorem completeSourceDensity_product_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder 𝔏]
    C (hD : 𝗕) (hq : 𝗘)
    (hM : 𝘧)
    Cfr lam ℓ N μ (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂)
    j
    h n (x : 𝙇) :
     ∫ e, highUnionActivation 𝔄 (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C 𝔄
        j h e (x i) ∂highUnionLaw 𝔄 (highCenterMix C) = 0 := by
  let a := C.densityLower+𝗙
  let b := C.densityUpper-𝗙
  let R := 𝔄
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr
     𝖡₄  lam ℓ N μ hℓ hℓN
  let β₀ : 𝙮 := ⟨𝖾,𝖢₄⟩
  let r₀ : HighResponseMarkIndex 𝙮 q := 𝖵₁
  exact highUnionSourceResetDensity_product_zero_of_density_projection C R
    (𝖠 ℓ N μ hCfr hℓ hℓN) hpos
    𝔊 SourceRowDensityMark
    𝔊 sourceRowDensityProj
    (𝔊 sourceRowDensityLift r₀)
    (𝔊 sourceRowDensityLift_measurable r₀)
    (𝔍 sourceRow_density_projection_slope r₀)
    (𝔍 sourceRow_density_projection_intercept r₀)
    (𝔍 sourceRow_density_observable_zero hpos) j h n x
