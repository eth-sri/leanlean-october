module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionInvariantMass
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The complete singleton, pair, and higher coarse/fine packet source
has a genuine time-independent raw mass law. -/
𝚫
𝚨
𝛆
𝚩
𝚬

variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder 𝙯]
    (C : ModelConstants d) (hD : 𝗕) (hq : 𝗘)
    (hM : highCenterResolutionThreshold C ≤ 𝖧)
    (Cfr lam ℓ N μ : ℝ) (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂)
include hD hq hM hCfr hℓ hℓN

𝗇 𝔄 𝖻 lam ℓ N μ
theorem completeSourceRows_mass_positive i :
    0 < (𝔄).rowMass i := by
  obtain ⟨ha,hab⟩ := 𝗌₁
  exact sourceRowMass_positive_actual d k D M q hD hq _ _ ha hab Cfr
     𝖡₄  lam ℓ N μ hℓ hℓN i

𝗇 𝔅 𝖫
𝗇 𝔇 𝚐
𝗇 𝔈 𝖠 ℓ N μ hCfr hℓ hℓN
𝗃 𝔐 ἀ C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
𝗇 𝔉 𝔐 completeSourceRows_mass_positive
𝗇 𝔊 T * (highRowTotalMass (𝔄).rowMass / highCenterMix C) / historyReferenceRho 𝔇 ≤ 1 / (2+8* (𝔇 : ℕ) ^2)
𝗇 𝔏 highUnionLaw 𝔄 $ highCenterMix C
𝗇 𝔍 historyMarkedPrior 𝔅 𝔇 t 𝔏 $ highUnionActivation 𝔄 $ highCenterMix C
section

variable (T)
    (hT : 𝚞)
    (hsmall : 𝔊)
    (t)
    (ht : t ∈ 𝗺)

include hT hsmall ht

/-- Probability of the actual full source path follows from its primitive
finite packet guards and the explicit history positivity budget. -/
theorem completeSourcePrior_probability :
    IsProbabilityMeasure 𝔍 :=
  highUnionSourcePrior_probability C _
    𝔈
    𝔉 T hT hsmall t ht

𝗇 𝔎 highUnionSourceMass C 𝔄
/-- Actual canonical append cancellation closes mass-law invariance for
all retained rows, including every higher coarse/fine target. -/
theorem completeSourceMass_prior_law :
    Measure.map 𝔎
      𝔍 =
    Measure.map 𝔎
      (historyMarkedReference 𝔅 𝔇
        𝔏) :=
  highUnionSourceMass_prior_law_of_append_annihilation C _
    𝔈
    𝔉
    T hT hsmall
    𝔐 completeSourceMass_append_indicator_zero t ht
