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
    let ratio := (2 * C * d + 8 * V * e) / d ^ 2
    let scale := 4 * C + 32 * V * H ^ 2
    ratio + (e / d) ^ 2 ≤
      (scale) / n + 4 * b ^ 4 := by
  intro ratio
  intro scale
  have hnsq : n ^ 2 ≤ 4 * d ^ 2 := by
    nlinarith
  have hfirst : 2 * C * n * d ≤ 4 * C * d ^ 2 := by
    have hp := mul_nonneg (mul_nonneg hC hd.le) (by linarith : 0 ≤ 2 * d - n)
    nlinarith
  have hsecond1 : 8 * V * n * e ≤ 8 * V * n ^ 2 * H ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left heH (by positivity)
    nlinarith
  have hsecond2 : 8 * V * n ^ 2 * H ^ 2 ≤ 32 * V * d ^ 2 * H ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ 8 * V * H ^ 2)
    nlinarith
  have hesq : e ^ 2 ≤ n ^ 2 * b ^ 4 := by
    nlinarith
  have hlhs : ratio + (e / d) ^ 2 =
      (2 * C * d + 8 * V * e + e ^ 2) / d ^ 2 := by
    rw [div_pow, ← add_div]
  have hrhs : (scale) / n + 4 * b ^ 4 =
      (scale + 4 * b ^ 4 * n) / n := by
    field_simp
  rw [hlhs, hrhs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hn).mpr
  nlinarith

variable {ι Ω : Type*} [Fintype ι]

/-- A uniform coordinate bound controls the residual energy regardless
of the cell approximation or the arrangement of the design points. -/
theorem projection_energy_le_uniform_bound
    {A : Matrix ι ι ℝ} (hsym : Aᵀ = A) (hidem : A * A = A)
    {f : ι → ℝ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ i, |f i| ≤ H) :
    projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * H ^ 2 := by
  apply (projection_energy_le hsym hidem f).trans
  calc
    _ ≤ ∑ _i, H ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := (sq_le_sq₀ (abs_nonneg _) hH).mpr (hf i)
      rw [sq_abs] at hs
      bound
    _ = _ := by simp

/-- The independent-error residual estimator has conditional risk
`C/n + 4 b^4` when half the sample remains as residual degrees of freedom.
Its approximation and uniform-size hypotheses are about the actual
regression vector, not about estimator risk or variance. -/
theorem independent_projection_half_degrees_mse
    [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Matrix ι ι ℝ}
    (hsym : Aᵀ = A) (hidem : A * A = A) (hn : 0 < Fintype.card ι)
    (hdegree : (Fintype.card ι) / 2 ≤ A.trace)
    {f : ι → ℝ} {ε : ι → Ω → ℝ} {V C₄ H b : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hf : ∀ i, |f i| ≤ H) (he : projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C₄) :
    (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - V) ^ 2 ∂μ) ≤
      (4 * max C₄ (2 * V ^ 2) + 32 * V * H ^ 2) / Fintype.card ι + 4 * b ^ 4 := by
  have hnreal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hd  := (half_pos hnreal).trans_le hdegree
  apply (independent_projection_estimator_mse_bound hsym hidem hd f
    hε hind hmean hsecond hfourth).trans
  exact projection_half_degrees_risk_algebra hnreal hd hdegree
    (projectionEnergy_nonneg _) (projection_energy_le_uniform_bound hsym hidem hH hf) he hV
    ((by positivity : 0 ≤ 2 * V ^ 2).trans (by bound))

end NearlyMinimax
