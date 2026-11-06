module

public import NearlyMinimax.HighUnionLikelihoodScore
public import NearlyMinimax.HighUnionInvariantMass
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine Borel reset primitives for the canonical full-union source. -/
𝚫
𝚪
𝚨
𝚭
𝛀
𝚬
𝚿

𝗇 𝔇 𝙯
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] [𝖭]
    [NeZero k] [LinearOrder 𝔇]
    (C : ModelConstants d) (R : 𝙭₁ I E)
    {M Cfr : ℝ} (G : 𝗗)

𝗇 𝔄 𝖫
𝗇 𝔅 𝗘₁
𝗇 𝔉 HistoryMarked 𝔄 $ HighUnionMark E
𝗇 𝔊 historyMarkedAppend 𝔄 𝔅 j 𝖷₁
/-- The actual density after appending the mark at the given window. -/
def highUnionSourceResetDensity (j : 𝔇)
    (h : 𝔉)
    (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highUnionSourceDensity C R 𝔊 x

/-- The actual reset coefficient vector at the selected window. -/
def highUnionSourceResetCoefficient (j : 𝔇)
    (h : 𝔉)
    (e : HighUnionMark E) : 𝙮 → ℝ :=
  highUnionResponseReset R e $ 𝖯 j

𝗇 𝔍 𝙾 x
include G in
theorem highUnionSourceDensity_coarse_interval
    (h : 𝔉)
    (x : Covariate d) : C.densityLower ≤ 𝔍 ∧
      𝔍 ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_interval C R G h x
  have hM : 𝚌 := by linarith [(𝚀₁ G.resolution).1]
  constructor <;> linarith [hb.1,hb.2,one_div_pos.mpr hM]

𝗇 𝔈 𝘖₁
include G in
theorem highUnionSourceResetDensity_measurable (j : 𝔇)
    (h : 𝔉) :
    Measurable $ Function.uncurry 𝔈 := by
  letI : 𝗄₁ := highUnionMark_standardBorel
  have ha : Measurable fun ex : HighUnionMark E × Covariate d =>
      historyMarkedAppend 𝔄
        𝔅 j (h,ex.1) :=
    (historyMarkedAppend_measurable (E := HighUnionMark E)
    𝔄
    𝔅 j).comp
      $ measurable_const.prodMk measurable_fst
  exact (highUnionSourceDensity_joint_measurable C R G).comp $ ha.prodMk measurable_snd

include G in
theorem highUnionSourceResetDensity_abs_le (j : 𝔇)
    (h : 𝔉)
    (e : HighUnionMark E) (x : Covariate d) :
    |𝔈 e x| ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_coarse_interval C R G
    𝔊 x
  rw [highUnionSourceResetDensity,abs_of_nonneg $ C.densityLower_pos.le.trans hb.1 ]
  exact hb.2

include G in
theorem highUnionSourceResetCoefficient_measurable (j : 𝔇)
    (h : 𝔉)
    (γ : 𝙮) :
    Measurable fun e => 𝚑₁ e γ := by
  unfold highUnionSourceResetCoefficient highUnionResponseReset coefficientReset
  exact (measurable_const.sub $ highUnionResponseTime_measurable R G.time_measurable ).mul
    measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
      $ highUnionResponseVector_measurable R G.vector_measurable γ )

theorem highUnionSourceResetDensity_outside j
    h
    e x (hx : x ∉ 𝘋) :
    𝔈 e x = 𝔍 :=
  highUnionSourceDensity_append_of_not_mem R C j h e x hx
