module

public import NearlyMinimax.HighResponseTensorTail
public import NearlyMinimax.CompleteSourceMassAnnihilation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! All-count response bounds on every actual row of the complete source
family. The density factors may depend on the full spatial carrier and
density atom, and are independent only of the response atom. -/
𝚸
𝚪
𝚨
𝚩
𝛈
𝚬

𝗇 𝔅 𝘀
𝗇 𝔐 𝙸
𝗇 𝔑 𝗳
𝗇 𝔜 𝙔
𝗇 𝔟 pPlus^n*highSeparatedDerivativeBudget a ρ
𝗃 𝔡 fun e => reset e ἀ
𝗃 𝔢 0 ≤ ἀ
𝗃 𝔤 ∑ γ, φ ἀ γ*v γ
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔇 𝔟*𝚍*𝙎
𝗇 𝔈 fun e i => (hmReset i).comp $ measurable_id.prodMk measurable_const
𝗇 𝔉 fun ζ e i => hReset 𝘕₂ i
𝗇 𝔊 ∀ γ δ, Measurable fun ζ => A ζ γ δ
𝗇 𝔍 fun ζ e => reset 𝘕₂
𝗇 𝔎 fun e => reset 𝘆₂
𝗇 𝔏 ∀ i, Measurable 𝔡 i
𝗃 𝔗 ἀ σ ad bd m r D q C A
𝗇 𝔓 𝔗 highPacketMarkMass
𝗇 𝔖 responseTensor_reference_all_count_bound σ q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
𝗇 𝔙 𝔤 i
theorem highPacket_reference_all_count_bound
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 𝗚)
    C a V η ρ pPlus (hC : 𝙴) (ha : 𝙆) (hη : 𝔢 η)
    (hρ : 𝔢 ρ) (hηρ : η ≤ 𝔐) (hpPlus : 𝔢 pPlus)
    A (hA : 𝔊)
    (hcost : 𝙧)
    (hpos : 0 < 𝔓)
    (reset : Z × HighDensityMarkIndex m r D → 𝔜)
    (hmReset : 𝔏)
    (hReset : ∀ e i, |reset e i| ≤ pPlus)
    g w φ c
    (hc : ∑ γ, |c γ| ≤ 𝔑) (hg : ∀ i, |g i| ≤ 𝔐) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝙛, ∑ γ, |v γ| ≤ 𝔑 → ∀ i, |𝔙| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔅) y :
    |highMarkedResponseAction 𝔗 highPacketAbsoluteLaw
      𝔗 highPacketActivation a V η
      𝔎
      (fun e => coefficientReset c 𝗻₁
        𝗼₁) g w φ y| ≤
      𝔇*
        𝔓 := 𝔖
    (densityPacketWeight ad bd m r D) A
    (highPacketMarkWeight_measurable ad bd m r D q C A hA)
    (𝔗 highPacketMarkWeight_integrable hA hcost) hpos
    𝔍
    𝔈
    𝔉 g w φ c hc hg hw hφ hp y

𝗃 𝔘 ἀ σ ad bd M q C A
theorem finePairPacket_reference_all_count_bound
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (M q : ℕ) (hn : 𝗚)
    C a V η ρ pPlus (hC : 𝙴) (ha : 𝙆) (hη : 𝔢 η)
    (hρ : 𝔢 ρ) (hηρ : η ≤ 𝔐) (hpPlus : 𝔢 pPlus)
    A (hA : 𝔊)
    (hcost : 𝙧)
    (hpos : 0 < 𝔘 finePairPacketMarkMass)
    (reset : Z × FinePairDensityIndex M → 𝔜)
    (hmReset : 𝔏)
    (hReset : ∀ e i, |reset e i| ≤ pPlus)
    g w φ c
    (hc : ∑ γ, |c γ| ≤ 𝔑) (hg : ∀ i, |g i| ≤ 𝔐) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝙛, ∑ γ, |v γ| ≤ 𝔑 → ∀ i, |𝔙| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔅) y :
    |highMarkedResponseAction 𝔘 finePairPacketAbsoluteLaw
      𝔘 finePairPacketActivation a V η
      𝔎
      (fun e => coefficientReset c (finePairPacketResponseVector M q C e)
        $ finePairPacketResponseTime M q e ) g w φ y| ≤
      𝔇*
        𝔘 finePairPacketMarkMass := 𝔖
    (finePairDensityWeight ad bd M) A
    (finePairPacketWeight_measurable ad bd M q C A hA)
    (𝔘 finePairPacketWeight_integrable hA hcost) hpos
    𝔍
    𝔈
    𝔉 g w φ c hc hg hw hφ hp y

end Packet

𝗇 𝔄 𝙴₂ ad bd C lam ℓ N μ
𝗇 𝔒 finePairTimeMatrix d 𝗀₂
𝗇 𝔔 𝗻
𝗇 𝔚 𝗱
𝗇 𝔛 highPacket_reference_all_count_bound 𝖶₁ ad bd D
𝗇 𝔞 𝖼₂
𝗃 𝔠 ἀ d D M q ad bd C lam ℓ N μ i
𝗃 𝔣 ἀ d r D lam i.val.2
/-- All rows of the actual complete source satisfy the same Taylor cap,
with their own true variation masses. In particular this holds for sample
counts exceeding the exterior selector degree. -/
theorem sourceRow_reference_all_count_bound
    (d : ℕ) [NeZero d] (k D M q : ℕ) (hn : 𝗚)
    (ad bd C lam ℓ N μ a V η ρ pPlus : ℝ)
    (hC : 𝙴) (ha : 𝙆) (hη : 𝔢 η) (hρ : 𝔢 ρ)
    (hηρ : η ≤ 𝔐) (hpPlus : 𝔢 pPlus)
    (hpos : ∀ i, 0 < (𝔄).rowMass i)
    i
    (reset : 𝔠 SourceRowDensityMark → 𝔜)
    (hmReset : ∀ u, Measurable 𝔡 u)
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    g w φ
    c (hc : ∑ γ, |c γ| ≤ 𝔑)
    (hg : ∀ u, |g u| ≤ 𝔐) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : 𝙮 → ℝ, ∑ γ, |v γ| ≤ 𝔑 →
      ∀ u, |𝔤 u| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝔅) y :
    |highMarkedResponseAction ((𝔄).rowLaw i)
      ((𝔄).rowActivation i) a V η
      (fun e => reset $ 𝔠 sourceRowDensityProj e )
      (fun e => coefficientReset c
        ((𝔄).rowVector i e)
        $ (𝔄).rowTime i e ) g w φ y| ≤
       𝔟*𝙒^2*𝙎 *
        (𝔄).rowMass i := by
  cases i with
  | inl p =>
    cases p
    · exact 𝔛 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        𝔔 𝔚 (integrable_const _)
        (hpos $ .inl .unit ) reset hmReset hReset g w φ c hc hg hw hφ hp y
    · exact highPacket_reference_all_count_bound (finePairTimeFieldMeasure d 0 ℓ) ad bd D 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        𝔒
        𝔞 (finePairTimeMatrix_cost_integrable d 0 ℓ _)
        (hpos $ .inl .coarse ) reset hmReset hReset g w φ c hc hg hw hφ hp y
    · exact finePairPacket_reference_all_count_bound (finePairTimeFieldMeasure d ℓ N) ad bd M q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        𝔒
        𝔞 (finePairTimeMatrix_cost_integrable d ℓ N _)
        (hpos $ .inl .fine ) reset hmReset hReset g w φ c hc hg hw hφ hp y
  | inr i =>
    cases i with
    | inl _ =>
      exact 𝔛 1 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        𝔔 𝔚 (integrable_const _)
        (hpos 𝘊₁) reset hmReset hReset g w φ c hc hg hw hφ hp y
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := 𝚁
      let T := 𝙽
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact highPacket_reference_all_count_bound (higherBandCarrierMeasure d r ℓ T i.val.2)
        ad bd m r D q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        𝔣 higherBandCarrierAmplitude
        𝔣 higherBandCarrierAmplitude_measurable
        (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2)
        (hpos 𝗱₁) reset hmReset hReset g w φ c hc hg hw hφ hp y
