module

public import NearlyMinimax.PairPilotAssumptions
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual numerator and the exact score identity for the paper's estimator. -/
𝚯
open scoped RealInnerProductSpace BigOperators
𝚨
𝚩
𝛃

namespace PairUStatistic
𝛡

𝗇 𝔄 (X i z.2, X j z.2)
𝗇 𝔅 (X j z.2, X i z.2)
theorem fieldPairAverage_add_smul n weight V
    G H (X : Fin n → Ω → E) (z : P × Ω) :
    fieldPairAverage n weight (fun p w => G p w + V * H p w) X z =
      fieldPairAverage n weight G X z + V * fieldPairAverage n weight H X z := by
  unfold fieldPairAverage pairAverage weightedSymmetrization
  simp
  have hpoint : ∀ i j ,
      weight / 4 * (G z.1 𝔄 + V * H z.1 𝔄 +
        (G z.1 𝔅 + V * H z.1 𝔅)) =
      weight / 4 * (G z.1 𝔄 + G z.1 𝔅) +
      V * (weight / 4 * (H z.1 𝔄 + H z.1 𝔅)) := by
    intros; ring
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end PairUStatistic

𝗇 𝔇 𝙩 → PairVector
𝗇 𝔈 sameLabelKernel (regularObservationLabel k hk) z
𝗇 𝔉 pairResponseVector z.1.2 z.2.2
𝗃 𝔊 pairPilotCoefficient bar η ἀ $ pairCovariates z
def pairPilotNumeratorKernel (k : ℕ) (hk : 𝖰)
    (bar : 𝔇)
    (η : Ω → 𝔇) (p : 𝚎)
    (z : 𝗰) : ℝ :=
  𝔈 *
    ⟪𝔊 p.1,
      InnerProductSpace.rankOne ℝ 𝔉
        𝔉
          𝔊 p.2⟫

theorem pairPilotNumeratorKernel_eq_score_add_noise
    (θ : RegressionParameter d) k hk
    bar
    (η : Ω → 𝔇) :
    pairPilotNumeratorKernel k hk bar η =
       fun p z => pairPilotScoreKernel θ k hk bar η p z +
        θ.variance * 𝖪₂ p z := by
  funext p z
  have hq : 𝔈 =
      sameLabelKernel 𝘯 (z.1.1, z.2.1) := rfl
  simp only [pairPilotNumeratorKernel, pairPilotScoreKernel, pairPilotNoiseKernel,
    pairScoreFieldKernel, pairNoiseFieldKernel, pairCovariates, pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_right, inner_smul_right]
  grind
