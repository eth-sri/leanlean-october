module

public import NearlyMinimax.GridMixtureRisk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! # The actual nonparametric low-smoothness lower bound

A concrete globally Hölder tent-window prior supplies admissible states in
original Model, its complete sample probability experiment, and a derived
score budget. Numeric grid rounding gives the paper's nonparametric rate.
-/
𝚫
𝛉
𝚨

𝚩

𝗇 𝔄 n ^ (-4 * C.smoothness / (d + 𝘊))
𝗇 𝔅 5 ^ (2 * C.smoothness)
𝗇 𝔇 lowSmoothnessAmplitude d C.smoothness G.b n
/-- The nonparametric low-smoothness minimax lower bound for all sample sizes
n≥1, proved in the original regression experiment without a rate premise. -/
theorem low_smoothness_nonparametric_minimax_lower (C : ModelConstants d)
    (hs1 : 𝘒₂) (hd : 𝘊 ≤ d) :
    ∃ c , 𝘝 ∧ ∀ n : ℕ, 𝗚 →
      ENNReal.ofReal (c * 𝔄) ≤
        𝚢 := by
  obtain ⟨G⟩ := lowSmoothnessPriorConstants_exists C
  refine ⟨G.b ^ 2 / (3 * 𝔅),
    div_pos (pow_pos G.b_pos 2) $ mul_pos  𝖠₄ 
      $ Real.rpow_pos_of_pos  𝖠₄  _ , ?_⟩
  intro n hn
  have hnR : 𝙠 ≤ n := by exact_mod_cast hn
  let k := lowSmoothnessGrid d C.smoothness n
  let η := 𝔇
  have hk : 𝗽₁ := by
    have hk4 := lowSmoothnessGrid_ge_four (d := d) C.smoothness_pos hnR
    omega
  have hg := lowSmoothness_amplitude_legal_guards C.smoothness_pos G.b_pos.le hnR
    G.field_guard G.variance_guard
  have hη := hg.1
  have hvariance := hg.2.2
  have hbudget : gridUniformScoreBudget G.ternary k n η ≤ 1 := by
    have hb := lowSmoothness_total_score_budget (d := d) C.smoothness_pos G.b_pos.le hnR
      $ lowSmoothnessScoreConstant_nonneg G.ternary
    have he : gridUniformScoreBudget G.ternary k n η =
        lowSmoothnessScoreConstant G.ternary *
          (𝙒 ^ 2 * 𝔇 ^ 4 /
            (lowSmoothnessGrid d C.smoothness n : ℝ) ^ d) := by
      dsimp [gridUniformScoreBudget, lowSmoothnessScoreConstant, k, η]
      ring
    rw [he]
    exact hb.trans G.score_guard
  have hprior := grid_prior_minimax_lower C G.ternary k η G.b hk hs1 G.b_pos.le hη
    hg.2.1 hvariance  𝖦₄  G.holder_guard (lowSmoothness_design_occupancy C.smoothness_pos hd hnR) hbudget
  have hseparation := lowSmoothness_variance_separation (d := d) (b := G.b)
    C.smoothness_pos hnR
  apply (ENNReal.ofReal_le_ofReal ?_).trans hprior
  calc
    _ = G.b ^ 2 / 𝔅 *
      𝔄 / 3 := 𝖢₃
    _ ≤ 𝙎 / 3 := div_le_div_of_nonneg_right hseparation 𝖠₄
