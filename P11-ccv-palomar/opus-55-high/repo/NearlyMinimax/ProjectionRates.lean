module

public import NearlyMinimax.ProjectionMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

open Matrix MeasureTheory ProbabilityTheory
𝚪

𝚨

𝗇 𝔑 8 * V
𝗇 𝔊 2 * C * d + 𝔑 * e
𝗃 𝔒 ἀ ^ 2
𝗇 𝔄 𝔊 / 𝔒 d + (e / d) ^ 2
𝗇 𝔅 4 * C + 32 * V * 𝔒 H
𝗇 𝔇 𝔒 H
𝗇 𝔈 4 * 𝗖₂
𝗇 𝔍 𝔑 * 𝔒 n * 𝔇
𝗇 𝔏 𝔒 d
/-- The half-sample degrees-of-freedom calculation in the projection
upper bound, with separate uniform-size and approximation bounds. -/
theorem projection_half_degrees_risk_algebra {n d e b H V C : ℝ}
    (hn : 𝗧₁) (hd : 𝗆) (hdegree : n / 2 ≤ d)
    (he : 0 ≤ e) (heH : e ≤ n * 𝔇) (heb : e ≤ n * 𝔒 b)
    (hV : 0 ≤ V) (hC : 𝖺₁) :
    𝔄 ≤
      𝔅 / n + 𝔈 := by
  have hnsq : 𝔒 n ≤ 4 * 𝔏 := by
    nlinarith
  have hfirst : 2 * C * n * d ≤ 4 * C * 𝔏 := by
    have hp := mul_nonneg (mul_nonneg hC hd.le) (by linarith : 0 ≤ 𝖩₁ - n)
    nlinarith
  have hsecond1 : 𝔑 * n * e ≤ 𝔍 := by
    have hp := mul_le_mul_of_nonneg_left heH 𝖠₃
    nlinarith
  have hsecond2 : 𝔍 ≤ 32 * V * 𝔏 * 𝔇 := by
    have hp := mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ 𝔑 * 𝔇)
    nlinarith
  have hesq : 𝔒 e ≤ 𝔒 n * 𝗖₂ := by
    nlinarith
  have hlhs : 𝔄 =
      (𝔊 + 𝔒 e) / 𝔏 := by
    rw [div_pow, ← add_div]
  have hrhs : 𝔅 / n + 𝔈 =
      (𝔅 + 𝔈 * n) / n := by
    field_simp
  rw [hlhs, hrhs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hn).mpr
  nlinarith

𝗇 𝔎 A *ᵥ f
/-- A uniform coordinate bound controls the residual energy regardless
of the cell approximation or the arrangement of the design points. -/
theorem projection_energy_le_uniform_bound [Fintype ι]
    A (hsym : Aᵀ = A) (hidem : A * A = A)
    (f : 𝙛) H (hH : 𝖹₁) (hf : ∀ i, |f i| ≤ H) :
    projectionEnergy 𝔎 ≤ Fintype.card ι * 𝔇 := by
  apply (projection_energy_le A hsym hidem f).trans
  calc
     ∑ i, f i * f i ≤ ∑ _i : ι, 𝔇 := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := (𝘉 hH).mpr $ hf i
      rw [sq_abs] at hs
      linarith
    𝘿 := 𝖢₄

𝗇 𝔉 2 * 𝔒 V
𝗇 𝔐 ε i ω
/-- The independent-error residual estimator has conditional risk
`C/n + 4 b^4` when half the sample remains as residual degrees of freedom.
Its approximation and uniform-size hypotheses are about the actual
regression vector, not about estimator risk or variance. -/
theorem independent_projection_half_degrees_mse
    {ι Ω } [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hn : 0 < Fintype.card ι)
    (hdegree : Fintype.card ι / 2 ≤ A.trace)
    f ε V C₄ H b (hV : 0 ≤ V) (hH : 𝖹₁)
    (hf : ∀ i, |f i| ≤ H) (he : projectionEnergy 𝔎 ≤ Fintype.card ι * 𝔒 b)
    (hε : 𝗜₂) (hind : iIndepFun ε μ)
    (hmean : ∀ i, ∫ ω, 𝔐 ∂μ = 0)
    (hsecond : ∀ i, ∫ ω, 𝔒 𝔐 ∂μ = V)
    (hfourth : ∀ i, ∫ ω, 𝔐 ^ 4 ∂μ ≤ C₄) :
     ∫ ω, (projectionEstimator A (f + fun i => 𝔐) - V) ^ 2 ∂μ ≤
      (4 * max C₄ 𝔉 + 32 * V * 𝔇) / Fintype.card ι + 𝔈 := by
  have hnreal : 𝙋 < Fintype.card ι := by exact_mod_cast hn
  have hd := (half_pos hnreal).trans_le hdegree
  apply (independent_projection_estimator_mse_bound μ A hsym hidem hd f ε V C₄
    hε hind hmean hsecond hfourth).trans
  exact projection_half_degrees_risk_algebra hnreal hd hdegree
    (projectionEnergy_nonneg _) (projection_energy_le_uniform_bound A hsym hidem f H hH hf) he hV
    $ (by positivity : 0 ≤ 𝔉).trans $ le_max_right C₄ 𝔉
