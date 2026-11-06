module

public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryAppendMeasurable
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Full-mark raw state updates for the actual ordinary/fine-pair union.
The data contain only the row laws and reset functions; all probability,
measurability, interval and coefficient conclusions are proved below. -/
𝛋
𝚪
𝚨
𝚩
𝚾
𝚬

𝗃 𝔚 (i : I) → E i → ἀ
𝗇 𝔅 𝔚 ℝ
𝗇 𝔇 𝙪
𝗇 𝔊 𝖲
𝗇 𝔍 𝗀
structure HighUnionRowData (d k F : ℕ) (I : Type*) (E : 𝔍)
    [𝔇] where
  rowLaw : (i : I) → Measure $ E i
  rowMass : 𝗦₂
  rowActivation : 𝔅
  rowIntercept : 𝔅
  rowSlope : 𝙯 → (i : I) → E i → 𝙀
  rowVector : 𝔚 𝔊
  rowTime : 𝔅

𝗇 𝔐 Sigma E ⊕ Unit
abbrev HighUnionMark (E : 𝔍) := 𝔐

𝗇 𝔈 𝖭
theorem highUnionMark_standardBorel {I : Type*} [Fintype I] {E : 𝔍}
    [𝔇] [𝔈] :
    𝗄₁ := by
  letI : StandardBorelSpace $ Sigma E := highRowReferenceUnion_standardBorel
  letI := upgradeStandardBorel $ Sigma E
  letI : BorelSpace 𝔐 := packetSum_borelSpace
  infer_instance

section Reset
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝔍}
  [𝔇] (R : 𝗽)

def highUnionLaw (δ : ℝ) : Measure $ HighUnionMark E :=
  highCenteredRowUnionLaw R.rowLaw R.rowMass δ

𝗇 𝔒 HighUnionMark E → ℝ
def highUnionActivation (δ : ℝ) : 𝔒 :=
  highCenteredRowUnionActivation R.rowMass R.rowActivation δ

def highUnionIntercept (δ : ℝ) : 𝔒 :=
  highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ

def highUnionSlope (j : 𝙯) (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e

𝗇 𝔑 𝖾
𝗃 𝔛 Sum.elim (fun e => ἀ e.1 e.2) 𝔑
def highUnionResponseVector : HighUnionMark E → 𝔊 :=
  𝔛 R.rowVector

def highUnionResponseTime : 𝔒 :=
  𝔛 R.rowTime

𝗃 𝔜 ἀ R e
𝗇 𝔓 𝔜 highUnionResponseVector
def highUnionResponseReset (e : HighUnionMark E) (c : 𝔊) :
    𝔊 :=
  coefficientReset c 𝔓 𝔜 highUnionResponseTime

𝗇 𝔔 HighRawState d k F
𝗃 𝔙 ἀ R δ
def highUnionRawUpdate (δ : ℝ) (j : 𝙯) (e : HighUnionMark E)
    (θ : 𝔔) : 𝔔 :=
  rawPatchUpdate j 𝘋 (highUnionSlope R j e)
    (fun _ => 𝔙 highUnionIntercept e) 𝔜 highUnionResponseReset θ

𝗇 𝔖 ∀ i, 0 ≤ R.rowMass i
theorem highUnionLaw_probability [∀ i, IsProbabilityMeasure $ R.rowLaw i ]
    (hMass : 𝔖) (hTotal : 0 < highRowTotalMass R.rowMass)
    δ (hδ0 : 𝚈) (hδ1 : δ ≤ 1) : IsProbabilityMeasure 𝔙 highUnionLaw :=
  highCenteredRowUnionLaw_probability R.rowLaw R.rowMass hMass hTotal δ hδ0 hδ1

𝗃 𝔎 ∀ i, Measurable $ ἀ i
theorem highUnionActivation_measurable (hAct : 𝔎 R.rowActivation) δ :
    Measurable 𝔙 highUnionActivation :=
  highCenteredRowUnionActivation_measurable R.rowMass R.rowActivation hAct δ

theorem highUnionActivation_centered (hMass : 𝔖)
    (hAct : 𝔎 R.rowActivation)
    (hiAct : ∀ i, Integrable (R.rowActivation i) $ R.rowLaw i )
    (hcAct : 𝗣₂)
    δ (hδ : 𝙮₂) (hδ1 : δ ≤ 1) :
     ∫ e, 𝔙 highUnionActivation e ∂𝔙 highUnionLaw = 0 :=
  highCenteredRowUnionActivation_centered R.rowLaw R.rowMass hMass R.rowActivation
    hAct hiAct hcAct δ hδ hδ1

theorem highUnionIntercept_measurable (hOffset : 𝔎 R.rowIntercept) δ :
    Measurable 𝔙 highUnionIntercept :=
  highCenteredRowUnionIntercept_measurable R.rowLaw R.rowMass R.rowIntercept hOffset δ

𝗇 𝔄 𝘥
theorem highUnionSlope_joint_measurable [𝔈]
    (hSlope : 𝔄)
    j :
    Measurable fun ex : HighUnionMark E × Covariate d => highUnionSlope R j ex.1 ex.2 := by
  let G : Sigma (fun i => E i × Covariate d) → ℝ := fun ex =>
    R.rowSlope j ex.1 ex.2.1 ex.2.2
  have hG := (historySigma_measurable_iff G).mpr $ hSlope j
  have hSigma :=
    hG.comp (historySigmaProdMeasurableEquiv E $ Covariate d ).measurable
  have h := (hSigma.sumElim $ measurable_const (a := 0) ).comp
    (MeasurableEquiv.sumProdDistrib (Sigma E) Unit $ Covariate d ).measurable
  convert h using 1
  bound

𝗇 𝔘 R.rowVector i e γ
𝗇 𝔉 ∀ i γ, Measurable fun e => 𝔘
theorem highUnionResponseVector_measurable
    (hVector : 𝔉) γ :
    Measurable fun e => 𝔓 γ :=
  (rowSigmaFunction_measurable (fun i e => 𝔘) fun i => hVector i γ ).sumElim
    measurable_const

theorem highUnionResponseTime_measurable (hTime : 𝔎 R.rowTime) :
    Measurable $ highUnionResponseTime R :=
  (rowSigmaFunction_measurable R.rowTime hTime).sumElim measurable_const

𝗇 𝔏 (highUnionResponseTime_measurable R hTime).comp measurable_fst
theorem highUnionRawUpdate_measurable [𝔈]
    (hSlope : 𝔄)
    (hOffset : 𝔎 R.rowIntercept)
    (hVector : 𝔉)
    (hTime : 𝔎 R.rowTime) δ j :
    Measurable fun eθ : HighUnionMark E × 𝔔 =>
      𝔙 highUnionRawUpdate j eθ.1 eθ.2 := by
  have hs x : Measurable fun e => highUnionSlope R j e x :=
    (highUnionSlope_joint_measurable R hSlope j).comp $ measurable_id.prodMk measurable_const
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro x
    by_cases hx : x ∈ 𝘋
    · simp only [affinePatchUpdate, if_pos hx]
      exact ((hs x).comp measurable_fst).mul
        ((measurable_pi_apply x).comp $ measurable_fst.comp measurable_snd ) |>.add
        ((highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    · simp only [affinePatchUpdate, if_neg hx]
      fun_prop
  · apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro γ
    by_cases hl : l = j
    · subst l
      simp only [responseCoordinateUpdate,
        Function.update_self]
      exact ((measurable_const.sub 𝔏).mul 𝖦₃ ).add
        $ (𝔏).mul
          $ (highUnionResponseVector_measurable R hVector γ).comp measurable_fst
    · simp only [responseCoordinateUpdate, Function.update_of_ne hl]
      fun_prop

𝗇 𝔗 𝗾₁
theorem highUnionResponseReset_ball Cfr (hCfr : 0 < Cfr)
    (hVector : ∀ i e, ∑ γ, |𝔘| ≤ 𝔗)
    (hTime : ∀ i e, R.rowTime i e ∈ 𝗃)
    e c
    (hc : ∑ γ, |c γ| ≤ 𝔗) :
     ∑ γ, |𝔜 highUnionResponseReset c γ| ≤ 𝔗 := by
  have hτ : 𝔜 highUnionResponseTime ∈ Icc 0 1 := by
    cases e with
    | inl e => exact hTime e.1 e.2
    | inr e => simp [highUnionResponseTime]
  have hv : ∑ γ, |𝔓 γ| ≤ 𝔗 := by
    cases e with
    | inl e => exact hVector e.1 e.2
    | inr e => simp [highUnionResponseVector, hCfr.le]
  exact coefficientReset_mem_ball Cfr c _ _ hτ hc hv
