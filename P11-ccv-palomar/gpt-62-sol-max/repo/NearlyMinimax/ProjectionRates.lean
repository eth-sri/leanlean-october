module

public import NearlyMinimax.ProjectionMoments


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NearlyMinimax

/-- The half-sample degrees-of-freedom calculation in the projection
upper bound, with separate uniform-size and approximation bounds. -/
theorem projection_half_degrees_risk_algebra {n d e b H V C : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hdegree : n / 2 ≤ d)
    (he : 0 ≤ e) (heH : e ≤ n * H ^ 2) (heb : e ≤ n * b ^ 2)
    (hV : 0 ≤ V) (hC : 0 ≤ C) :
    (2 * C * d + 8 * V * e) / d ^ 2 + (e / d) ^ 2 ≤
      (4 * C + 32 * V * H ^ 2) / n + 4 * b ^ 4 := by
  calc
    _ = 2 * C / d + 8 * V * (e / d ^ 2) + (e / d) ^ 2 := by field_simp <;> ring
    _ ≤ 2 * C / (n / 2) + 8 * V * ((n * H ^ 2) / (n / 2) ^ 2) +
          ((n * b ^ 2) / (n / 2)) ^ 2 := by gcongr
    _ = _ := by field_simp <;> ring

/-- A uniform coordinate bound controls the residual energy regardless
of the cell approximation or the arrangement of the design points. -/
theorem projection_energy_le_uniform_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (f : ι → ℝ) (H : ℝ) (hf : ∀ i, |f i| ≤ H) :
    projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * H ^ 2 :=
  (projection_energy_le A hsym hidem f).trans (projectionEnergy_le_of_abs_le f H hf)

/-- The independent-error residual estimator has conditional risk
`C/n + 4 b^4` when half the sample remains as residual degrees of freedom.
Its approximation and uniform-size hypotheses are about the actual
regression vector, not about estimator risk or variance. -/
theorem independent_projection_half_degrees_mse
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hn : 0 < Fintype.card ι)
    (hdegree : (Fintype.card ι : ℝ) / 2 ≤ A.trace)
    (f : ι → ℝ) (ε : ι → Ω → ℝ) (V C₄ H b : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hf : ∀ i, |f i| ≤ H) (he : projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C₄) :
    (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - V) ^ 2 ∂μ) ≤
      (4 * max C₄ (2 * V ^ 2) + 32 * V * H ^ 2) / Fintype.card ι + 4 * b ^ 4 := by
  have hnreal : (0 : ℝ) < Fintype.card ι := by positivity
  have hd := (half_pos hnreal).trans_le hdegree
  apply (independent_projection_estimator_mse_bound μ A hsym hidem hd f ε V C₄
    hε hind hmean hsecond hfourth).trans
  exact projection_half_degrees_risk_algebra hnreal hd hdegree
    (projectionEnergy_nonneg _) (projection_energy_le_uniform_bound A hsym hidem f H hf) he hV
    ((by positivity : (0 : ℝ) ≤ 2 * V ^ 2).trans (le_max_right C₄ (2 * V ^ 2)))

end NearlyMinimax
