module

public import NearlyMinimax.PairConditionalLaw
public import NearlyMinimax.ResponseOperatorMean


@[expose] public section

/-! The quadratic response means for arbitrary measurable pilot coefficient
fields under the paper's actual observation law. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ)
    {cA cB : Covariate d × Covariate d → PairVector} {q : Covariate d × Covariate d → ℝ}

def pairScoreFieldKernel (θ : RegressionParameter d)
    (cA cB : Covariate d × Covariate d → PairVector)
    (q : Covariate d × Covariate d → ℝ) (z : Observation d × Observation d) : ℝ :=
  q (z.1.1, z.2.1) * ⟪cA (z.1.1, z.2.1),
    pairScoreOperator θ.variance z.1.2 z.2.2 (cB (z.1.1, z.2.1))⟫

include hθ in
theorem pairScoreFieldKernel_mean
    (hi : Integrable (pairScoreFieldKernel θ cA cB q)
      ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, pairScoreFieldKernel θ cA cB q z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x, q x * ⟪cA x,
        InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression x.1) (θ.regression x.2))
          (pairResponseVector (θ.regression x.1) (θ.regression x.2)) (cB x)⟫
        ∂(designLaw θ).prod (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  rw [observationPair_integral_conditioning hθ hi]
  apply integral_congr_ae
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae
      hθ.2.2.2.2.2.2.2,
    (Measure.quasiMeasurePreserving_snd).ae
      hθ.2.2.2.2.2.2.2] with x hx hx'
  have hμ  :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hx.2.1
  change (∫ u, q x * ⟪cA x,
    pairScoreOperator θ.variance (θ.regression x.1 + u.1) (θ.regression x.2 + u.2) (cB x)⟫
      ∂(θ.errors x.1).prod (θ.errors x.2)) = _
  rw [integral_const_mul, conditional_pairScoreOperator_integral
    hμ ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hx'.2.1) hx.2.2.2.1 hx'.2.2.2.1 hx.2.2.2.2.1 hx'.2.2.2.2.1]

def pairNoiseFieldKernel
    (cA cB : Covariate d × Covariate d → PairVector)
    (q : Covariate d × Covariate d → ℝ) (z : Observation d × Observation d) : ℝ :=
  q (z.1.1, z.2.1) * ⟪cA (z.1.1, z.2.1), pairNoiseOperator (cB (z.1.1, z.2.1))⟫

include hθ in
theorem pairNoiseFieldKernel_mean
    (hi : Integrable (pairNoiseFieldKernel cA cB q)
      ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, pairNoiseFieldKernel cA cB q z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x, q x * ⟪cA x, pairNoiseOperator (cB x)⟫
        ∂(designLaw θ).prod (designLaw θ) := by
  rw [observationPair_integral_conditioning hθ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ _u, q x * ⟪cA x, pairNoiseOperator (cB x)⟫
    ∂(θ.errors x.1).prod (θ.errors x.2)) = _
  simp

end NearlyMinimax
