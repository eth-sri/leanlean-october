module

public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.HighFrameEvaluation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual original-model legality of complete-row canonical raw histories.
The density is normalized by its true integrated mass, and the regression
uses the actual periodic polynomial field of the history's reset coefficients. -/
𝚸
𝚪
𝚨
𝚩
𝚾
𝚬

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝙪] [NeZero k] [LinearOrder 𝙯]
  (C : ModelConstants d) (R : 𝗽)

𝗇 𝔄 𝖫
def highUnionSourceRegression (η : ℝ)
    (h : HistoryMarked 𝔄 $ HighUnionMark E )
    (x : Covariate d) : ℝ :=
  highFrameField d k η (fun j => highFramePolynomial $ 𝖯 j ) x

theorem highUnionSourceState_measurable [𝖭]
    (G : 𝗗) :
    Measurable $ highUnionSourceState C R :=
  historyMarkedRawState_measurable 𝔄
    (highUnionRawUpdate R $ highCenterMix C )
    ( highUnionRawUpdate_measurable R G.slope_measurable G.intercept_measurable
      G.vector_measurable G.time_measurable $ highCenterMix C ) highUnionVacuum

theorem highUnionSourceRegression_joint_measurable [𝖭]
    (G : 𝗗) η :
    Measurable fun hx : HistoryMarked 𝔄
      (HighUnionMark E) × Covariate d => highUnionSourceRegression C R η hx.1 hx.2 :=
by
  let Ω := HistoryMarked 𝔄
    $ HighUnionMark E
  exact highFrameField_joint_measurable d k F η
    (fun h => 𝖯) $ measurable_snd.comp $ highUnionSourceState_measurable C R G
