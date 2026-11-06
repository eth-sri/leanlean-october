module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.MixtureRisk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual tilted observable means are the means under the observed-data
mixture kernel, on the original real sample space. -/
𝚹
𝚨
𝚭
𝚩
𝛂

𝗇 𝔄 highRealSampleKernel n a V p F hp hF ∘ₘ massPowerTilt ν 𝙙 n
theorem highTiltedObservableMean_eq_dataMean (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V aRaw bRaw B : ℝ) (ha : 𝙞) (haRaw : 𝙓) (hB : 𝙐)
    (p F : Ω → 𝙀)
    hp hF
    (hraw : 𝙄)
    (hq : ∀ ω x y, 0 ≤ 𝙅 V y)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    highTiltedObservableMean ν n a V p F hp hF H =
      ∫ z, H z ∂𝔄 := by
  have hb ω :=
    𝙕
  let _ := massPowerTilt_isProbability ν _ 𝙨 n aRaw bRaw haRaw hb
  let _ := highRealSampleKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have hi : Integrable H 𝔄 := by
    apply Integrable.of_bound hH.aestronglyMeasurable B
    simp_all
  exact (probability_kernel_integral _ _ H hi).symm
