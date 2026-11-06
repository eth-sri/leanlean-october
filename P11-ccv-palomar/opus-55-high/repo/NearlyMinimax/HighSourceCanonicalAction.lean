module

public import NearlyMinimax.HighSourceUnionAction
public import NearlyMinimax.HighSourceRawDecomposition
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact canonical complete-source append action, converted to the
manuscript's genuine ordinary and fine-pair signed first actions. -/
𝚸
𝚪
𝚨
𝚩
set_option maxHeartbeats 1800000
𝚬
𝚿

𝗇 𝔄 congrArg fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1)
𝗃 𝔙 highUnionSourceResetDensity C R j h ἀ $ x u
𝗇 𝔅 ∏ u, 𝔙 e
𝗇 𝔇 1/𝖧
𝗇 𝔈 𝗋₁
𝗇 𝔔 R.rowSlope j i e $ x u
𝗇 𝔉 𝔔*p u+𝘅₂
𝗇 𝔊 𝖻 lam ℓ N μ
𝗇 𝔍 𝚑₁ e
𝗇 𝔎 𝖯 j
𝗇 𝔏 sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ
𝗇 𝔐 highLocalCoordinates d k j $ x u
𝗇 𝔑 𝙾 $ x u
𝗇 𝔒 x u ∈ 𝘋
𝗇 𝔓 C.densityUpper^n*B
𝗃 𝔖 O $ Sum.inl ⟨Sum.inl ἀ,e⟩
𝗃 𝔗 ἀ d D M q ad bd Cfr lam ℓ N μ
𝗃 𝔘 ἀ C R G j h
𝗃 𝔚 ἀ ad bd D q Cfr p c Φ
theorem completeSourceCanonicalAction_eq_signed_first_action
    {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder 𝙯]
    (C : ModelConstants d) (hD : 𝗕) (hq : 𝗘)
    (hM : highCenterResolutionThreshold C ≤ 𝖧)
    (Cfr lam ℓ N μ : ℝ) (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂)
    (j : 𝙯)
    h
    (x : 𝙇) (hx : ∀ u, 𝔒)
    Φ (hmΦ : Measurable Φ)
    (B : ℝ) (hB : 𝙐) (hΦ : ∀ v : 𝙮 → ℝ,
       ∑ γ, |v γ| ≤ 𝗾₁ → |Φ v| ≤ B) :
    let R := 𝔊
     ∫ e, 𝗾 e*
      (𝔅*
        Φ 𝔍) ∂𝗛 =
      completeSourceSignedFirstAction (C.densityLower+𝔇)
        (C.densityUpper-𝔇) lam ℓ N μ D M q Cfr
        (fun u => 𝔐)
        (fun u => 𝔑) 𝔎 Φ := by
  dsimp only
  let ad := C.densityLower+𝔇
  let bd := C.densityUpper-𝔇
  let R := 𝔊
  let G := 𝖠 ℓ N μ hCfr hℓ hℓN
  let c := 𝔎
  let p := fun u : Fin n => 𝔑
  let U := fun u : Fin n => 𝔐
  let O := fun e => 𝔅*
    Φ 𝔍
  letI : StandardBorelSpace $ HighUnionMark 𝔗 SourceRowMark :=
    highUnionMark_standardBorel
  have hc := 𝘛₁ j
  have hmCoef :=
    measurable_pi_iff.mpr 𝔘 highUnionSourceResetCoefficient_measurable
  have hmO : Measurable O := (Finset.measurable_fun_prod _ fun u _ =>
    (𝔘 highUnionSourceResetDensity_measurable).comp
      $ measurable_id.prodMk measurable_const ).mul $ hmΦ.comp hmCoef
  have hOb e : ‖O e‖ ≤ 𝔓 := by
    change |𝔅*Φ _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (finite_density_product_abs_bound _ C.densityUpper
      (lt_trans zero_lt_one C.one_lt_densityUpper).le
       fun u => 𝔘 highUnionSourceResetDensity_abs_le e $ x u )
      (hΦ _ $ highUnionResponseReset_ball R Cfr  𝖡₄  G.vector_ball G.time_interval e c hc )
      (abs_nonneg _) $ pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le n
  have hreset i e u :
      𝔙 𝔈 =
      𝔉 := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append]
    change (if 𝔒 then 𝔔*_+𝘅₂ else _) = _
    rw [if_pos $ hx u ]
    dsimp only [p]
    unfold highUnionSourceDensity
    rfl
  have hO i e :
      O 𝔈 = (∏ u, 𝔉)*
        Φ (coefficientReset c (R.rowVector i e) $ R.rowTime i e ) := by
    simp only [O,hreset,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [completeSourceUnion_signed_action C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN O hmO
    𝔓 hOb]
  change ∑ i : 𝔗 SourceRowIndex,
      ∫ᵛ e, O 𝔈 ∂<•𝔏 i =
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q Cfr U p c Φ
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have hunit : ∫ᵛ e, 𝔖 FinePairRowTag.unit
      ∂<•𝔏 (.inl .unit) =
      𝔚 finePairUnitFirstAction := by
    unfold finePairUnitFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply 𝔄
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset]
    ring
  have hcoarse : ∫ᵛ e, 𝔖 FinePairRowTag.coarse
      ∂<•𝔏 (.inl .coarse) =
      finePairCoarseFirstAction ad bd ℓ D q Cfr U p c Φ := by
    unfold finePairCoarseFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply 𝔄
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset,U]
    ring
  have hfine : ∫ᵛ e, 𝔖 FinePairRowTag.fine
      ∂<•𝔏 (.inl .fine) =
      finePairFineFirstAction ad bd ℓ N M q Cfr U p c Φ := by
    unfold finePairFineFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply 𝔄
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,finePairPacketSlope,finePairPacketIntercept,
      finePairPacketObservable,finePairDensityReset,U]
    ring
  have hsingle : ∫ᵛ e, O (Sum.inl ⟨Sum.inr $ Sum.inl () ,e⟩)
      ∂<•𝔏 𝘊₁ =
      𝔚 singletonFirstAction := by
    unfold singletonFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply 𝔄
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,singletonRowData,
      highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset]
    ring
  have hhigher i :
       ∫ᵛ e, O (Sum.inl ⟨Sum.inr $ Sum.inr i ,e⟩)
        ∂<•𝔏 𝗱₁ =
      higherBandFirstAction ad bd lam ℓ 𝙽
        (higherBandFamilyTarget i.val) 𝚁 D q Cfr i.val.2 U p c Φ := by
    unfold higherBandFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply 𝔄
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,higherBandFamilyComponent,
      higherBandRowData,highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset,U]
    ring
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit,.coarse,.fine} := 𝖨₃
  simp only [htags]
  simp [hunit,hcoarse,hfine,hsingle,hhigher,Fintype.sum_unique,
    completeSourceSignedFirstAction,finePairThreeRowFirstAction,add_assoc]
