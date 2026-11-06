module

public import NearlyMinimax.HighUnionSource
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact locality of the complete-row canonical source reset. -/
𝚸
𝚨
𝚩
𝚬

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝙪]
  (R : 𝗽)

theorem highUnionRawUpdate_density_of_not_mem δ
    j e θ
    x (hx : x ∉ 𝘋) :
    (highUnionRawUpdate R δ j e θ).1 x = θ.1 x := by
  simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]

variable [NeZero k] [LinearOrder 𝙯] (C : ModelConstants d)

theorem highUnionSourceState_append j
    h
    e :
    highUnionSourceState C R 𝘾 =
    highUnionRawUpdate R (highCenterMix C) j e (highUnionSourceState C R h) :=
  highUnionMarkedState_append R _ highUnionVacuum j h e

/-- Appending a full source mark leaves every density value outside that
label's physical patch exactly unchanged. -/
theorem highUnionSourceDensity_append_of_not_mem j
    h
    e x (hx : x ∉ 𝘋) :
    highUnionSourceDensity C R 𝘾 x =
    𝙾 x := by
  change (highUnionSourceState C R _).1 x = _
  rw [highUnionSourceState_append R C j h e]
  exact highUnionRawUpdate_density_of_not_mem R _ j e _ x hx
