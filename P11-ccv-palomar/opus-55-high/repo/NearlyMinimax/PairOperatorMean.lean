module

public import NearlyMinimax.PairConditionalLaw
public import NearlyMinimax.ResponseOperatorMean
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The quadratic response means for arbitrary measurable pilot coefficient
fields under the paper's actual observation law. -/
𝚯
𝚻
𝚨
𝚩

𝗇 𝔅 𝙩
𝗇 𝔇 (z.1.1, z.2.1)
def pairScoreFieldKernel (θ : RegressionParameter d)
    (cA cB : 𝔅 → PairVector)
    (q : 𝔅 → ℝ) (z : 𝗰) : ℝ :=
  q 𝔇 * ⟪cA 𝔇,
    pairScoreOperator θ.variance z.1.2 z.2.2 $ cB 𝔇 ⟫

𝗇 𝔄 𝖶
𝗇 𝔈 pairResponseVector (θ.regression x.1) $ θ.regression x.2
𝗇 𝔊 𝖱
𝗇 𝔍 (θ.errors x.1).prod $ θ.errors x.2
𝗇 𝔎 pairScoreFieldKernel θ cA cB q
𝗃 𝔏 (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ἀ
theorem pairScoreFieldKernel_mean C
    θ (hθ : 𝙟)
    cA cB
    q
    (hi : Integrable 𝔎
      𝔄) :
     ∫ z, 𝔎 z ∂𝔄 =
      ∫ x : 𝔅, q x * ⟪cA x,
        InnerProductSpace.rankOne ℝ 𝔈
          𝔈 $ cB x ⟫
        ∂𝔊 := by
  let := 𝘪₁
  rw [observationPair_integral_conditioning C θ hθ _ hi]
  apply integral_congr_ae
  filter_upwards [𝘳₂
      hθ.2.2.2.2.2.2.2,
    𝘴₂
      hθ.2.2.2.2.2.2.2] with x hx hx'
  change ∫ u : 𝚑, q x * ⟪cA x,
    pairScoreOperator θ.variance (θ.regression x.1 + u.1) (θ.regression x.2 + u.2) $ cB x ⟫
      ∂𝔍 = _
  rw [integral_const_mul, conditional_pairScoreOperator_integral (θ.errors x.1) (θ.errors x.2)
    𝔏 hx.2.1 𝔏 hx'.2.1 hx.2.2.2.1 hx'.2.2.2.1 hx.2.2.2.2.1 hx'.2.2.2.2.1]

def pairNoiseFieldKernel
    (cA cB : 𝔅 → PairVector)
    (q : 𝔅 → ℝ) (z : 𝗰) : ℝ :=
  q 𝔇 * ⟪cA 𝔇, pairNoiseOperator $ cB 𝔇 ⟫

𝗇 𝔉 q x * ⟪cA x, pairNoiseOperator $ cB x ⟫
theorem pairNoiseFieldKernel_mean C
    θ (hθ : 𝙟)
    cA cB
    q
    (hi : Integrable (pairNoiseFieldKernel cA cB q)
      𝔄) :
     ∫ z, pairNoiseFieldKernel cA cB q z ∂𝔄 =
      ∫ x : 𝔅, 𝔉
        ∂𝔊 := by
  rw [observationPair_integral_conditioning C θ hθ _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change ∫ _u : 𝚑, 𝔉
    ∂𝔍 = _
  simp
