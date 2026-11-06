module

public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HistoryPatchStateAppend
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine complete-union canonical histories: Borel raw states, legal
density and coefficient values, and pointwise/total reference mean one. -/
𝛋
𝚨
𝚩
𝚱
𝚬

𝗇 𝔄 𝘥
𝗇 𝔡 highUnionIntercept R δ e
𝗇 𝔅 fun _ e _ => 𝔡
𝗇 𝔈 ∀ i, Measurable $ R.rowIntercept i
𝗇 𝔉 fun _ => highUnionResponseReset R
𝗃 𝔣 ἀ d k
𝗇 𝔏 𝔣 HighRawState F
𝗇 𝔑 𝖭
𝗇 𝔗 𝔣 HighWindowLabels
𝗇 𝔛 𝙪
𝗇 𝔢 highUnionRawUpdate R δ
section Finite
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝔛] (R : 𝔣 HighUnionRowData F I E)

𝗇 𝔍 fun θ i => 𝔢 (labels i) (marks i) θ
𝗇 𝔞 Fin n → HighUnionMark E
def highUnionHistoryState (δ : ℝ) (n : ℕ) (labels : Fin n → 𝔗)
    (initial : 𝔏) (marks : 𝔞) : 𝔏 :=
  (List.ofFn fun i : Fin n => i ).foldl
    𝔍 initial

𝗇 𝔎 𝘞₁
𝗇 𝔔 𝔣 highTorusPatch
theorem highUnionHistory_density_joint_measurable [𝔑]
    (hSlope : 𝔄)
    (hOffset : 𝔈) δ
    n labels
    initial (hi : Measurable initial.1) :
    Measurable fun mx : 𝔞 × Covariate d =>
      (highUnionHistoryState R δ n labels initial mx.1).1 mx.2 := affinePatchFold_density_joint_measurable 𝔔
    𝔣 highTorusPatch_measurableSet (highUnionSlope R)
    𝔅
    ( highUnionSlope_joint_measurable R hSlope )
    (fun _ => (highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    𝔉 n labels 𝔎
    (fun _ => initial) $ hi.comp measurable_snd

𝗇 𝔊 x ∈ 𝔣 highTorusPatch j
𝗇 𝔒 R.rowSlope j i e x
𝗇 𝔓 highUnionHistoryState R δ n labels initial marks
𝗇 𝔖 hSlope j x
𝗇 𝔘 𝘔₂
𝗇 𝔜 fun e => 𝔒
𝗇 𝔟 hiSlope j x
𝗃 𝔤 ∫ e, ἀ j e ∂π
𝗃 𝔦 ∀ j, Integrable (ἀ j) π
𝗃 𝔧 highRowReferenceUnion_integrable R.rowLaw R.rowMass _ $ rowSigmaFunction_measurable _ ἀ
𝗃 𝔨 ἀ 𝔔 (highUnionSlope R) 𝔅 𝔉 labels
/-- Finite independent complete-union marks preserve pointwise density
mean one. Raw row slopes are centered by their actual absolute-law reflection
rules; the single global correction gives offset mean one. -/
theorem highUnionHistory_density_mean_one [∀ i, IsProbabilityMeasure $ R.rowLaw i ]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hSlope : ∀ j x i, Measurable 𝔜)
    (hiSlope : ∀ j x i, Integrable 𝔜 $ R.rowLaw i )
    (hcSlope : ∀ j x i, ∫ e, 𝔒 ∂ R.rowLaw i = 0)
    (hOffset : 𝔈)
    a b (hOffsetBound : ∀ i e, 𝘅₂ ∈ 𝔘)
    δ (hδ0 : 𝚈) (hδ1 : δ < 1)
    n labels
    initial (hinit : 𝗅₂) x :
    (∫ marks, (𝔓).1 x
      ∂Measure.pi fun _ => highUnionLaw R δ ) = 1 := by
  let π := highUnionLaw R δ
  letI := highUnionLaw_probability R hMass hTotal δ hδ0 hδ1.le
  let s := fun j e =>
    if 𝔊 then highUnionSlope R j e x else 1
  let o := fun j e =>
    if 𝔊 then 𝔡 else 0
  have hs : 𝔦 s := by
    intro j
    by_cases hx : 𝔊
    · simp only [s, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _
        (highCenteredRowUnionSlope_measurable _ 𝔖)
        $ 𝔧 𝔖 𝔟
    aesop
  have ho : 𝔦 o := by
    intro j
    by_cases hx : 𝔊
    · simp only [o, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _ (highUnionIntercept_measurable R hOffset δ)
        $ 𝔧 hOffset
           fun i => boundedIntercept_integrable (R.rowLaw i) (R.rowIntercept i)
            (hOffset i) a b $ hOffsetBound i
    aesop
  have hmean : ∀ j, 𝔤 s + 𝔤 o = 1 := by
    intro j
    by_cases hx : 𝔊
    · simp only [s, o, if_pos hx]
      change ∫ e, highCenteredRowUnionSlope (fun i e => 𝔒) e
        ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ +
         ∫ e, highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ e
          ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ = 1
      rw [highCenteredRowUnionSlope_integral_zero R.rowLaw R.rowMass hMass hTotal
          _ 𝔖 𝔟 (hcSlope j x) δ hδ0 hδ1.le,
        highCenteredRowUnionIntercept_integral_one R.rowLaw R.rowMass hMass hTotal
          R.rowIntercept hOffset a b hOffsetBound δ hδ0 hδ1]
      norm_num
    aesop
  convert finiteAffineHistory_integral_one π s o hs ho hmean n labels using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro marks
  exact (𝔨 affinePatchFold_density_eq marks 𝔎 initial x).trans $ by tauto

theorem highUnionHistory_density_interval δ a b
    (hLegal : ∀ j e x v, v ∈ 𝔘 →
      highUnionSlope R j e x * v + 𝔡 ∈ 𝔘)
    n labels initial
    (hi : ∀ x, initial.1 x ∈ 𝔘) marks x :
    (𝔓).1 x ∈ 𝔘 :=
  𝔨 affineRawHistory_density_interval 𝔎 marks a b hLegal initial hi x

𝗇 𝔙 𝗾₁
theorem highUnionHistory_coefficient_ball δ Cfr (hCfr : 0 < Cfr)
    (hVector : ∀ i e, ∑ γ, |R.rowVector i e γ| ≤ 𝔙)
    (hTime : ∀ i e, R.rowTime i e ∈ 𝗃)
    n labels initial
    (hi : ∀ j, ∑ γ, |initial.2 j γ| ≤ 𝔙) marks :
    ∀ j, ∑ γ, |(𝔓).2 j γ| ≤ 𝔙 := by
  have hf : ∀ indices : List $ Fin n , ∀ initial ,
      (∀ j, ∑ γ, |initial.2 j γ| ≤ 𝔙) → ∀ j,
       ∑ γ, |(indices.foldl 𝔍
        initial).2 j γ| ≤ 𝔙 := by
    intro indices
    induction indices with
    | nil => intro initial hi j; exact hi j
    | cons i indices ih =>
      intro initial hi
      apply ih
      intro j
      by_cases hj : j = labels i
      · subst j
        change ∑ γ, |(Function.update initial.2 (labels i)
          $ highUnionResponseReset R (marks i) $ initial.2 $ labels i ) (labels i) γ| ≤ _
        rw [Function.update_self]
        exact highUnionResponseReset_ball R Cfr hCfr hVector hTime _ _ $ hi _
      · simpa only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
          Function.update_of_ne hj] using hi j
  bound

end Finite

section Canonical
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝔛] [NeZero k] [LinearOrder 𝔗]
  (R : 𝔣 HighUnionRowData F I E)
  (dependent : 𝔗 → 𝔗 → Prop)

𝗇 𝔐 HistoryMarked dependent $ HighUnionMark E
def highUnionMarkedState (δ : ℝ) (initial : 𝔏)
    (h : 𝔐) : 𝔏 :=
  historyMarkedRawState dependent 𝔢 initial h

𝗃 𝔥 ἀ R dependent δ initial
def highUnionMarkedDensity (δ : ℝ) (initial : 𝔏)
    (h : 𝔐) (x : Covariate d) : ℝ :=
  (𝔥 highUnionMarkedState h).1 x

𝗇 𝔚 𝔥 highUnionMarkedDensity
def highUnionMarkedMass (δ : ℝ) (initial : 𝔏)
    (h : 𝔐) : ℝ :=
  ∫ x, 𝔚 h x ∂cubeVolume d

𝗇 𝔠 𝗠₁
theorem highUnionMarkedDensity_joint_measurable [𝔑]
    (hSlope : 𝔄)
    (hOffset : 𝔈) δ
    initial (hi : Measurable initial.1) :
    Measurable fun hx : 𝔐 × Covariate d =>
      𝔚 hx.1 hx.2 := by
  letI : 𝗄₁ := highUnionMark_standardBorel
  let X := fun g =>
    Fin 𝔠 → HighUnionMark E
  let G : Sigma (fun g => X g × Covariate d) → ℝ := fun hx =>
    𝔚 ⟨hx.1,hx.2.1⟩ hx.2.2
  have hG : Measurable G := by
    apply (historySigma_measurable_iff G).mpr
    intro g
    exact highUnionHistory_density_joint_measurable R hSlope hOffset δ
      𝔠 𝘤₂ initial hi
  exact hG.comp (historySigmaProdMeasurableEquiv X $ Covariate d ).measurable

theorem highUnionMarkedMass_measurable [𝔑]
    (hSlope : 𝔄)
    (hOffset : 𝔈) δ
    initial (hi : Measurable initial.1) :
    Measurable 𝔥 highUnionMarkedMass := by
  letI := cubeVolume_isProbability d
  exact (highUnionMarkedDensity_joint_measurable R dependent hSlope hOffset δ initial hi).stronglyMeasurable.integral_prod_right'.measurable

𝗇 𝔇 fun i j => j ∈ 𝔣 highNeighborLabels i
theorem highUnionMarkedState_append [NeZero k] δ initial
    j
    h
    fresh :
    highUnionMarkedState R 𝔇 δ initial
      (historyMarkedAppend 𝔇
        (fun {_ _} h => 𝔣 highNeighborLabels_symmetric _ _ h) j 𝘥₂) =
      𝔢 j fresh
        (highUnionMarkedState R 𝔇 δ initial h) :=
  𝔣 highMarkedRawState_patch_append (highUnionSlope R)
    𝔅 𝔉 initial j h fresh
