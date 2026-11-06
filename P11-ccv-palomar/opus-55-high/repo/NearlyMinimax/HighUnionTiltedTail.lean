module

public import NearlyMinimax.HighUnionInvariantMass
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual complete-row mass-power tilt is a probability measure;
the source bounded-differences MGF gives its exceptional mass probability. -/
𝚫
𝚨
𝚭
𝚩
𝚬

𝗃 𝔄 ἀ d k
section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] [𝖭]
    [NeZero k] [LinearOrder 𝔄 HighWindowLabels]
    (C : ModelConstants d) (R : 𝔄 HighUnionRowData F I E)
    {M Cfr : ℝ} (G : 𝗗)
include G

𝗃 𝔅 ἀ C R G
𝗇 𝔉 highUnionSourceMass C R
theorem highUnionSourceMass_coarse_interval
    h :
    𝔉 h ∈ Icc C.densityLower C.densityUpper := by
  have hg := 𝚀₁ G.resolution
  have hM0 : 𝚌 := 𝖡₄
  have hb := 𝔅 highUnionSourceMass_interval h
  constructor
  · exact (le_add_of_nonneg_right (one_div_pos.mpr hM0).le).trans hb.1
  · exact hb.2.trans $ sub_le_self _ (one_div_pos.mpr hM0).le

𝗇 𝔇 𝗛
𝗇 𝔈 8*𝔄 highHistoryMassParameter C.densityLower C.densityUpper
𝗇 𝔊 𝚐
/-- Actual complete-union reference fiber means and true torus block
oscillation yield the mass-tilted exceptional probability. -/
theorem highUnionSourceMass_reference_tilted_tail (hk : 𝚂) (n : ℕ) ε
    (hε : 𝔈*n ≤ ε) :
    (massPowerTilt
      (historyMarkedReference (fun i j => j ∈ 𝔄 highNeighborLabels i) 𝔊
        𝔇) 𝔉 n).real
      {h | ε < |𝔉 h-1|} ≤
      2*Real.exp (-ε^2/𝔈) := by
  letI := 𝔅 highUnionSourceLaw_probability
  letI := historyMarkedReference_probability _ 𝔄 highNeighborLabels_self_mem
    (fun {_ _} h => 𝔄 highNeighborLabels_symmetric _ _ h) 𝔊
    (one_le_pow₀ 𝖠₄ ) 𝔄 highNeighbor_dependency_card
    𝔇
  exact massPowerTilt_abs_tail _ _ 𝔅 highUnionSourceMass_measurable n
    C.densityLower C.densityUpper C.densityLower_pos 𝔅 highUnionSourceMass_coarse_interval
    𝔅 highUnionSourceMass_reference_mean_one _ ε
    (𝔄 highHistoryMassParameter_pos _ _  𝖡₃ 
      $ C.densityLower_lt_one.trans C.one_lt_densityUpper )
    (𝔅 highUnionSourceMass_reference_mgf hk) hε

end Generic

section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder 𝔄 HighWindowLabels]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 𝗕) (hq : 𝗘) (hM : highCenterResolutionThreshold C ≤ 𝖧)
    (hCfr : 𝗹) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN
