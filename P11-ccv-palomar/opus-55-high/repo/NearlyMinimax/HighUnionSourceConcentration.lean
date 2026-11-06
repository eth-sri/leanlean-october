module

public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.HighHistoryInvariantMass
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The true complete-union canonical mass has mean one and the exact
source grid concentration parameter under the infinite reference law. -/
𝚫
𝚪
𝚨
𝚩
𝚾
𝚬

section
𝗃 𝔍 ἀ d k
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝙪] [𝖭]
  [NeZero k] [LinearOrder 𝔍 HighWindowLabels]
  (C : ModelConstants d) (R : 𝔍 HighUnionRowData F I E)
  {M Cfr : ℝ} (G : 𝗗)
include G

𝗇 𝔄 fun i j => j ∈ 𝔍 highNeighborLabels i
𝗇 𝔅 𝗛
𝗇 𝔇 fun {_ _} h => 𝔍 highNeighborLabels_symmetric _ _ h
𝗇 𝔈 𝚐
𝗇 𝔉 highUnionSourceMass C R
𝗃 𝔊 ἀ C R G
𝗇 𝔎 (𝚀₁ G.resolution).1
theorem highUnionSourceMass_reference_mean_one :
     ∫ h, 𝔉 h
      ∂historyMarkedReference 𝔄 𝔈
        𝔅 = 1 := by
  letI := 𝔊 highUnionSourceLaw_probability
  apply historyMarkedReference_mean_one 𝔄
    𝔍 highNeighborLabels_self_mem 𝔇
    𝔈 (one_le_pow₀ 𝖠₄ ) 𝔍 highNeighbor_dependency_card
    𝔅 𝔉
    𝔊 highUnionSourceMass_measurable C.densityUpper _
    𝔊 highUnionSourceMass_fiber_mean_one
  intro h
  have hp := 𝔊 highUnionSourceMass_interval h
  have hM0 : 𝚌 := by
    have := 𝔎
    linarith
  rw [abs_of_nonneg $ by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0] ]
  linarith [hp.2, one_div_pos.mpr hM0]

theorem highUnionSourceMass_reference_mgf (hk : 𝚂) u :
     ∫ h, Real.exp (u * (𝔉 h-1))
      ∂historyMarkedReference 𝔄 𝔈
        𝔅 ≤
      Real.exp (𝔍 highHistoryMassParameter C.densityLower C.densityUpper * 𝙟₁) := by
  letI := 𝔊 highUnionSourceLaw_probability
  have hBound : ∀ h, |𝔉 h| ≤ C.densityUpper := by
    intro h
    have hp := 𝔊 highUnionSourceMass_interval h
    have hM0 : 𝚌 := by
      have := 𝔎
      linarith
    rw [abs_of_nonneg $ by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0] ]
    linarith [hp.2, one_div_pos.mpr hM0]
  have hgap : 0 ≤ C.densityUpper-C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have h := historyMarkedReference_mass_mgf 𝔄
    𝔍 highNeighborLabels_self_mem 𝔇
    𝔈 (one_le_pow₀ 𝖠₄ ) 𝔍 highNeighbor_dependency_card
    𝔅 𝔉 𝔊 highUnionSourceMass_measurable C.densityUpper
    (𝗄 * (C.densityUpper-C.densityLower))  𝖠₃ 
    hBound 𝔊 highUnionSourceMass_fiber_mean_one
    (fun g j marks marks' hMarks => 𝔊 highUnionSourceMass_block_oscillation hk g marks marks' j hMarks) u
  convert h using 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  unfold highHistoryMassParameter
  ring
