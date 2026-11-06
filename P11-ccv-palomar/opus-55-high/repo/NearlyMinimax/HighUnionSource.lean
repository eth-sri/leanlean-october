module

public import NearlyMinimax.HighUnionHistory
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Source constant specialization for complete-row canonical histories.
The guard fields are primitive actual row-law identities and finite atomic
reset bounds; history expectations and original-model legality are outputs. -/
𝛋
𝚨
𝚩
𝚱
𝚬

𝗇 𝔞 C.densityLower + 𝗙
𝗇 𝔟 C.densityUpper - 𝗙
𝗇 𝔄 Icc 𝔞 𝔟
𝗇 𝔍 R.rowSlope j i e x
𝗇 𝔖 𝙪
𝗃 𝔡 ∀ i, Measurable $ ἀ i
𝗃 𝔢 ἀ d k
structure HighUnionSourceGuards {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝔖] (C : ModelConstants d) (M Cfr : ℝ)
    (R : 𝔢 HighUnionRowData F I E) : Prop where
  resolution : 𝘧
  frame : 𝗹
  row_probability : ∀ i, IsProbabilityMeasure $ R.rowLaw i
  mass_nonneg : ∀ i, 0 ≤ R.rowMass i
  total_positive : 0 < highRowTotalMass R.rowMass
  activation_measurable : 𝔡 R.rowActivation
  activation_bound : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i
  activation_centered : 𝗣₂
  slope_measurable : 𝘥
  slope_integrable : ∀ j x i, Integrable (fun e => 𝔍) $ R.rowLaw i
  slope_centered : ∀ j x i, ∫ e, 𝔍 ∂ R.rowLaw i = 0
  intercept_measurable : 𝔡 R.rowIntercept
  intercept_interval : ∀ i e, 𝘅₂ ∈
    𝔄
  row_reset_interval : ∀ j i e x v, v ∈ 𝔄 →
    𝔍 * v + 𝘅₂ ∈
      𝔄
  vector_measurable : ∀ i γ, Measurable fun e => R.rowVector i e γ
  time_measurable : 𝔡 R.rowTime
  vector_ball : ∀ i e, ∑ γ, |R.rowVector i e γ| ≤ 𝗾₁
  time_interval : ∀ i e, R.rowTime i e ∈ Icc 𝙋 1

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝔖] [NeZero k] [LinearOrder 𝔢 HighWindowLabels]
  (C : ModelConstants d) (R : 𝔢 HighUnionRowData F I E)

def highUnionVacuum : 𝔢 HighRawState F := (𝙃, 0)

𝗇 𝔠 𝔢 highNeighborLabels i
𝗇 𝔅 fun i j => j ∈ 𝔠
𝗇 𝔏 HistoryMarked 𝔅 $ HighUnionMark E
def highUnionSourceState
    (h : 𝔏) :
    𝔢 HighRawState F :=
  highUnionMarkedState R 𝔅 (highCenterMix C)
    highUnionVacuum h

𝗃 𝔑 ἀ C R
def highUnionSourceDensity
    (h : 𝔏)
    (x : Covariate d) : ℝ := (𝔑 highUnionSourceState h).1 x

𝗇 𝔗 𝔑 highUnionSourceDensity h
def highUnionSourceMass
    (h : 𝔏) : ℝ :=
  ∫ x, 𝔗 x ∂cubeVolume d

variable {M Cfr : ℝ} (G : 𝗗)
include G

𝗃 𝔒 ἀ R $ highCenterMix C
𝗇 𝔐 𝔒 highUnionLaw
theorem highUnionSourceLaw_probability : IsProbabilityMeasure 𝔐 := by
  letI := G.row_probability
  exact highUnionLaw_probability R G.mass_nonneg G.total_positive _
    (𝘗₁).le (highCenterMix_mem C).2.le

theorem highUnionSource_reset_interval j e
    x v (hv : v ∈ 𝔄) :
    highUnionSlope R j e x * v + 𝔒 highUnionIntercept e ∈
      𝔄 := by
  letI := G.row_probability
  exact highCenteredRowUnion_reset_source_legal C R.rowLaw R.rowMass
    G.mass_nonneg G.total_positive (fun i e => 𝔍) R.rowIntercept
    G.intercept_measurable M G.resolution G.intercept_interval
    (fun i e v hv => G.row_reset_interval j i e x v hv) e v hv

𝗇 𝔘 𝚀₁ G.resolution
theorem highUnionSource_vacuum_interval :
     1 ∈ 𝔄 := by
  have hm := 𝔘
  have hr := highCenterRadius_le_margins C
  constructor <;> linarith [highCenterRadius_pos C]

𝗃 𝔥 𝔑 ἀ G
𝗇 𝔎 fun _ => 𝔥 highUnionSource_vacuum_interval
𝗇 𝔙 𝔥 highUnionSource_reset_interval
𝗇 𝔚 historyShapeLength _ h.1
𝗇 𝔛 historyShapeCanonicalLabels _ h.1
theorem highUnionSourceDensity_interval
    h x :
    𝔗 x ∈ 𝔄 :=
  𝔒 highUnionHistory_density_interval _ _
    𝔙 𝔚
    𝔛 highUnionVacuum
    𝔎 h.2 x

theorem highUnionSourceState_coefficient_ball
    h :
    ∀ j, ∑ γ, |(𝔑 highUnionSourceState h).2 j γ| ≤ 𝗾₁ := 𝔒 highUnionHistory_coefficient_ball Cfr
    (by linarith [G.frame]) G.vector_ball G.time_interval 𝔚
    𝔛 highUnionVacuum
    (fun _ => by simpa [highUnionVacuum] using
       inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr) ) h.2

𝗇 𝔈 𝖭
𝗃 𝔣 ἀ R 𝔅 G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const
theorem highUnionSourceDensity_joint_measurable [𝔈] :
    Measurable fun hx : 𝔏 × Covariate d => 𝔑 highUnionSourceDensity hx.1 hx.2 :=
  𝔣 highUnionMarkedDensity_joint_measurable

theorem highUnionSourceMass_measurable [𝔈] :
    Measurable 𝔑 highUnionSourceMass :=
  𝔣 highUnionMarkedMass_measurable

𝗇 𝔇 Measure.pi fun _ : Fin $ historyShapeLength _ g => 𝔐
𝗇 𝔉 historyShapeLength _ g
𝗇 𝔊 fun i j => j ∉ 𝔠
𝗃 𝔤 ⟨g,ἀ⟩
𝗇 𝔓 𝔤 marks
𝗇 𝔔 historyShapeCanonicalLabels _ g
theorem highUnionSourceDensity_fiber_mean_one
    (g : HistoryShape 𝔊)
    x :
     ∫ marks, 𝔑 highUnionSourceDensity 𝔓 x
      ∂𝔇 = 1 := by
  letI := G.row_probability
  exact highUnionHistory_density_mean_one R G.mass_nonneg G.total_positive
    (fun j x i => (G.slope_measurable j i).comp $ measurable_id.prodMk measurable_const )
    G.slope_integrable G.slope_centered G.intercept_measurable _ _ G.intercept_interval
    (highCenterMix C) (𝘗₁).le (highCenterMix_mem C).2
    𝔉 𝔔 highUnionVacuum 𝘦 x

theorem highUnionSourceMass_interval [𝔈]
    h :
    𝔑 highUnionSourceMass h ∈ 𝔄 := by
  letI := cubeVolume_isProbability d
  exact boundedIntercept_mean_mem (cubeVolume d) 𝔗
    ((𝔥 highUnionSourceDensity_joint_measurable).comp $ measurable_const.prodMk measurable_id )
    _ _ $ 𝔥 highUnionSourceDensity_interval h

𝗇 𝔜 Fin 𝔉 → HighUnionMark E
theorem highUnionSourceMass_fiber_mean_one [𝔈]
    (g : HistoryShape fun i j : 𝔢 HighWindowLabels => j ∉ 𝔠 ) :
     ∫ marks, 𝔑 highUnionSourceMass 𝔓
      ∂𝔇 = 1 := by
  letI := 𝔥 highUnionSourceLaw_probability
  letI := cubeVolume_isProbability d
  let f := fun mx : 𝔜 × Covariate d =>
    𝔑 highUnionSourceDensity 𝔤 mx.1 mx.2
  have hm : Measurable f := highUnionHistory_density_joint_measurable R G.slope_measurable
    G.intercept_measurable (highCenterMix C) 𝔉
    𝔔 highUnionVacuum measurable_const
  have hM0 : 𝚌 := by
    have := (𝔘).1
    linarith
  have hi : Integrable f $ (Measure.pi fun _ =>
      𝔐 ).prod $ cubeVolume d := by
    apply (integrable_const C.densityUpper).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro mx
    have hb := 𝔥 highUnionSourceDensity_interval 𝔤 mx.1 mx.2
    rw [Real.norm_eq_abs, abs_of_nonneg $ by
      dsimp [f]; linarith [hb.1, C.densityLower_pos, one_div_pos.mpr hM0] ]
    exact hb.2.trans $ by linarith [one_div_pos.mpr hM0]
  change ∫ marks, ∫ x, f (marks,x) ∂cubeVolume d
    ∂𝔇 = 1
  rw [integral_integral_swap hi]
  have he (x : Covariate d) :
       ∫ marks, f (marks,x) ∂𝔇 = 1 := 𝔥 highUnionSourceDensity_fiber_mean_one g x
  simp_all

theorem highUnionSourceMass_block_oscillation [𝔈] (hk : 𝚂)
    (g : HistoryShape 𝔊)
    (marks marks' : 𝔜) j
    (hMarks : ∀ i, 𝔔 i ≠ j → 𝘢₂) :
    |𝔑 highUnionSourceMass 𝔓 - 𝔑 highUnionSourceMass 𝔤 marks'| ≤
      𝗄 * (C.densityUpper-C.densityLower) := by
  have h := 𝔢 highAffineMarkedMass_block_oscillation hk
    𝔅 (highUnionSlope R)
    (fun _ e _ => 𝔒 highUnionIntercept e)
    (fun j e => (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      $ measurable_const.prodMk measurable_id ) 𝗱
    (fun _ => highUnionResponseReset R) 𝔞 𝔟
    (by linarith [(𝔥 highUnionSource_vacuum_interval).1,
      (𝔥 highUnionSource_vacuum_interval).2])
    𝔙 highUnionVacuum measurable_const
    𝔎 g marks marks' j hMarks
  apply h.trans
  have hM0 : 𝚌 := by
    have := (𝔘).1
    linarith
  apply mul_le_mul_of_nonneg_left _ 𝖠₃
  linarith [one_div_pos.mpr hM0]
