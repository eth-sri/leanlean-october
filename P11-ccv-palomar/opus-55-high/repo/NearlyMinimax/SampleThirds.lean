module

public import NearlyMinimax.SampleRemainder
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Two pilots and one evaluation block from arbitrary original sample sizes. -/
𝚯
𝚮
𝚨
𝚩

def threeBlockSize (n : ℕ) : ℕ := n / 3

𝗇 𝔇 threeBlockSize n + threeBlockSize n + threeBlockSize n
def threeBlockRemainder (n : ℕ) : ℕ := n - 𝔇

theorem threeBlockTotal n :
    n = 𝔇 + threeBlockRemainder n := by
  simp only [threeBlockSize, threeBlockRemainder]
  omega

section

variable (hn : 6 ≤ n)

include hn

theorem threeBlockSize_two_le : 2 ≤ threeBlockSize n := by
  unfold threeBlockSize
  omega

theorem threeBlockSize_fraction :
    (𝚡 : ℝ) * n ≤ threeBlockSize n := by
  have hR : n ≤ 4 * 𝚝 := by exact_mod_cast by unfold threeBlockSize; omega
  linarith

end

def castEstimator (h : n = m) (T : Estimator d m) : 𝚠 := h.symm ▸ T

theorem castEstimator_risk_eq (h : n = m) T
    (θ : RegressionParameter d) : meanSquaredRisk (castEstimator h T) θ = meanSquaredRisk T θ := by
  subst m
  rfl

𝗇 𝔄 Fin (threeBlockSize n) → Observation d
def threeBlockEstimator
    (T : (𝔄 × 𝔄) ×
      𝔄 → ℝ) (hmT : Measurable T) : 𝚠 :=
  castEstimator (threeBlockTotal n)
    $ blockEstimatorWithRemainder (r := threeBlockRemainder n) T hmT

𝗇 𝔅 sampleLaw θ $ threeBlockSize n
theorem threeBlockEstimator_risk_eq C
    (θ : RegressionParameter d) (hθ : 𝙟)
    T hmT :
    meanSquaredRisk (threeBlockEstimator T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((𝔅).prod 𝔅).prod
          𝔅 := by
  rw [threeBlockEstimator, castEstimator_risk_eq]
  exact blockEstimatorWithRemainder_risk_eq C θ hθ T hmT
