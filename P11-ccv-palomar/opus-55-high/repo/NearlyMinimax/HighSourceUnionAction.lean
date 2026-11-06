module

public import NearlyMinimax.HighCompleteSourceTail
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Conversion of the true positive activated complete-source reference
law into the genuine signed atom packets. All spatial/field carriers and
finite response marks remain in their actual signed measures. -/
𝚸
𝚪
𝚨
𝛀
𝛈
𝚬

𝗇 𝔄 finePairTimeMatrix d 𝗀₂
𝗇 𝔇 𝗻
𝗇 𝔉 𝖶₁
𝗃 𝔛 ἀ d ℓ N
𝗇 𝔔 𝔛 higherBandFamilyUpper μ i.val
𝗇 𝔖 𝗱₁
𝗃 𝔙 ἀ d D M q a b C lam ℓ N μ
𝗃 𝔚 ἀ 𝔉 a b D
def sourceRowSignedMeasure (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : 𝔙 SourceRowIndex) →
      SignedMeasure $ 𝔙 SourceRowMark i
  | .inl .unit => 𝔚 highPacketSignedMeasure 2 D q C
      𝔇
  | .inl .coarse => highPacketSignedMeasure (finePairTimeFieldMeasure d 0 ℓ) a b D 2 D q C
      𝔄
  | .inl .fine => finePairPacketSignedMeasure 𝔛 finePairTimeFieldMeasure a b M q C
      𝔄
  | .inr $ .inl _ => 𝔚 highPacketSignedMeasure 1 D q C
      𝔇
  | 𝔖 => higherBandSignedRow d (higherBandFamilyTarget i.val)
      𝚁 D q a b C lam ℓ
      𝔔 i.val.2

𝗃 𝔑 ἀ d k D M q
𝗇 𝔅 𝔑 sourceRowData a b C lam ℓ N μ
𝗇 𝔈 𝗱
𝗇 𝔊 𝖼₂
𝗇 𝔎 higherBandCarrierAmplitude_measurable d r D lam i.val.2
𝗃 𝔐 ἀ a b D 2 D q C
𝗇 𝔒 𝘛₂
𝗇 𝔓 (𝔉).prod Measure.count
theorem sourceRow_activated_signed_action (d : ℕ) [NeZero d] k D M q
    a b C lam ℓ N μ
    (hpos : ∀ i, 0 < (𝔅).rowMass i)
    i
    F (hF : Measurable F)
    L (hFbound : 𝔒) :
     ∫ e, (𝔅).rowActivation i e * F e
      ∂(𝔅).rowLaw i =
      ∫ᵛ e, F e ∂<•𝔑 sourceRowSignedMeasure a b C lam ℓ N μ i := by
  cases i with
  | inl p =>
    cases p
    · exact absoluteMarkLaw_signed_action 𝔓
        (𝔐 highPacketMarkWeight 𝔇)
        (𝔚 highPacketMarkWeight_integrable 2 D q C _
          𝔈 $ integrable_const _ )
        (𝔐 highPacketMarkWeight_measurable _ 𝔈)
        (hpos $ .inl .unit ) F hF L hFbound
    · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d 0 ℓ).prod Measure.count)
        (𝔐 highPacketMarkWeight 𝔄)
        (highPacketMarkWeight_integrable _ a b D 2 D q C _ 𝔊
          $ finePairTimeMatrix_cost_integrable d 0 ℓ _ )
        (𝔐 highPacketMarkWeight_measurable _ 𝔊)
        (hpos $ .inl .coarse ) F hF L hFbound
    · exact absoluteMarkLaw_signed_action ((𝔛 finePairTimeFieldMeasure).prod Measure.count)
        (finePairPacketWeight a b M q C 𝔄)
        (finePairPacketWeight_integrable _ a b M q C _ 𝔊
          $ 𝔛 finePairTimeMatrix_cost_integrable _ )
        (finePairPacketWeight_measurable a b M q C _ 𝔊)
        (hpos $ .inl .fine ) F hF L hFbound
  | inr i =>
    cases i with
    | inl _ =>
      exact absoluteMarkLaw_signed_action 𝔓
        (highPacketMarkWeight a b D 1 D q C 𝔇)
        (𝔚 highPacketMarkWeight_integrable 1 D q C _
          𝔈 $ integrable_const _ )
        (highPacketMarkWeight_measurable a b D 1 D q C _ 𝔈)
        (hpos 𝘊₁) F hF L hFbound
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := 𝚁
      let T := 𝔔
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact absoluteMarkLaw_signed_action ((higherBandCarrierMeasure d r ℓ T i.val.2).prod Measure.count)
        (highPacketMarkWeight a b m r D q C $ higherBandCarrierAmplitude d r D lam i.val.2 )
        (highPacketMarkWeight_integrable _ a b m r D q C _
          𝔎
          $ higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2 )
        (highPacketMarkWeight_measurable a b m r D q C _
          𝔎)
        (hpos 𝔖) F hF L hFbound

𝗇 𝔍 𝖻 lam ℓ N μ
𝗇 𝔏 𝗋₁
𝗇 𝔗 C.densityLower+𝗙
𝗇 𝔘 C.densityUpper-𝗙
/-- The entire canonical source generator is an actual finite sum of
its constructed signed packet integrals, with numerical source guards. -/
theorem completeSourceUnion_signed_action {d k D M q : ℕ} [NeZero d]
    C (hD : 𝗕) (hq : 𝗘)
    (hM : 𝘧)
    Cfr lam ℓ N μ (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂)
    F (hF : Measurable F)
    L (hFbound : 𝔒) :
    let R := 𝔍
     ∫ e, 𝗾 e*F e ∂𝗛 =
      ∑ i, ∫ᵛ e, F 𝔏
        ∂<•𝔑 sourceRowSignedMeasure 𝔗
          𝔘 Cfr lam ℓ N μ i := by
  dsimp
  let a := 𝔗
  let b := 𝔘
  let R := 𝔍
  let G := 𝖠 ℓ N μ hCfr hℓ hℓN
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hpos := 𝔑 sourceRowMass_positive_actual hD hq a b ha hab Cfr
     𝖡₄  lam ℓ N μ hℓ hℓN
  rw [highUnionSource_bounded_action C R G hpos F hF L hFbound]
  apply Finset.sum_congr rfl
  intro i _
  exact 𝔑 sourceRow_activated_signed_action a b Cfr lam ℓ N μ hpos i
    (fun e => F 𝔏)
    (hF.comp $ measurable_inl.comp $ rowSigmaMk_measurable i ) L fun e => hFbound _
