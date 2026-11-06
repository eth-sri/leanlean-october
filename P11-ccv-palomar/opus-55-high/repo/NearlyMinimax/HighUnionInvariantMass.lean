module

public import NearlyMinimax.FinePairUnionMassAnnihilation
public import NearlyMinimax.HighUnionSourceConcentration
public import NearlyMinimax.HighHistoryInvariantMass
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine complete-union source prior probability, invariant mass law,
and the original mass-power-tilted exceptional probability bound. -/
𝚫
𝚪
𝚨
𝚭
𝚩
𝚬

𝗃 𝔎 ἀ d k
section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] [𝖭]
    [NeZero k] [LinearOrder 𝔎 HighWindowLabels]
    (C : ModelConstants d) (R : 𝔎 HighUnionRowData F I E)
    {M Cfr : ℝ} (G : 𝗗)
    (hpos : 𝚣)
include G hpos

𝗇 𝔅 𝗾
𝗇 𝔐 𝘗₁
𝗇 𝔔 𝗰₁
theorem highUnionSourceActivation_bound e :
    |𝔅 e| ≤
      𝔔 :=
  highCenteredRowUnionActivation_bound R.rowMass hpos G.total_positive R.rowActivation
    G.activation_bound _ 𝔐 e

𝗇 𝔄 𝗛
theorem highUnionSourceActivation_centered :
     ∫ e, 𝔅 e ∂𝔄 = 0 := by
  letI := G.row_probability
  exact highUnionActivation_centered R G.mass_nonneg G.activation_measurable
    (fun i => Integrable.of_bound (G.activation_measurable i).aestronglyMeasurable (R.rowMass i)
      $ Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using G.activation_bound i e )
    G.activation_centered _ 𝔐 (highCenterMix_mem C).2.le

𝗇 𝔖 𝚐
𝗇 𝔇 T * 𝔔 / historyReferenceRho 𝔖 ≤ 1 / (2 + 8 * (𝔖 : ℕ) ^2)
𝗇 𝔈 fun i j => j ∈ 𝔎 highNeighborLabels i
𝗇 𝔉 fun {_ _} h => 𝔎 highNeighborLabels_symmetric _ _ h
𝗇 𝔊 𝔖
𝗃 𝔗 ἀ C R G
𝗇 𝔍 𝔗 highUnionSourceActivation_bound hpos
section

variable (T)
    (hT : 𝚞)
    (hsmall : 𝔇)

include hT hsmall

𝗇 𝔏 historyMarkedPrior 𝔈 𝔊 t 𝔄 𝔅
𝗇 𝔑 𝔗 highUnionSourceActivation_centered hpos
𝗇 𝔓 div_nonneg G.total_positive.le (𝔐).le
/-- The actual complete tagged union, with its one corrective branch,
produces a genuine probability source path under the source positivity budget. -/
theorem highUnionSourcePrior_probability t (ht : t ∈ 𝗺) :
    IsProbabilityMeasure 𝔏 := by
  letI := 𝔗 highUnionSourceLaw_probability
  have hm := highUnionActivation_measurable R G.activation_measurable $ highCenterMix C
  have hB :=
    𝔓
  have hi : Integrable 𝔅
      𝔄 :=
    Integrable.of_bound hm.aestronglyMeasurable _ $ Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using 𝔍 e
  have hs :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB)
      (historyReferenceRho_pos _).le).trans hsmall
  exact historyMarkedPrior_probability _ 𝔎 highNeighborLabels_self_mem
    𝔉 𝔊
    (one_le_pow₀ 𝖠₄ ) 𝔎 highNeighbor_dependency_card
    t _ ht.1 hB _ _ hi 𝔑
    𝔍 hs

𝗇 𝔒 highUnionSourceMass C R
/-- Structural response-summed packet annihilation implies the true
complete-union canonical mass pushforward is constant in time. -/
theorem highUnionSourceMass_prior_law_of_append_annihilation (hkill : ∀ j h S, MeasurableSet S →
       ∫ e, S.indicator 𝘋₁
        (𝔒 $ historyMarkedAppend
          𝔈
          𝔉 j 𝖷₁ ) *
        𝔅 e ∂𝔄 = 0)
    t (ht : t ∈ 𝗺) :
    Measure.map 𝔒
      𝔏 =
    Measure.map 𝔒
      (historyMarkedReference 𝔈 𝔊
        𝔄) := by
  letI := 𝔗 highUnionSourceLaw_probability
  letI : 𝗄₁ := highUnionMark_standardBorel
  exact historyMarkedPrior_invariant_law _ 𝔎 highNeighborLabels_self_mem
    𝔉 𝔊
    (one_le_pow₀ 𝖠₄ ) 𝔎 highNeighbor_dependency_card
    T _ hT 𝔓
    𝔄 𝔅
    (highUnionActivation_measurable R G.activation_measurable _)
    𝔑 𝔍
    hsmall _ 𝔗 highUnionSourceMass_measurable hkill t ht

end

end Generic

section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder 𝔎 HighWindowLabels]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 𝗕) (hq : 𝗘) (hM : highCenterResolutionThreshold C ≤ 𝖧)
    (hCfr : 𝗹) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN
