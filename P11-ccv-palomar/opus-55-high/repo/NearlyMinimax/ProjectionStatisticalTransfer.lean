module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ProjectionStatistical
public import NearlyMinimax.PolynomialGridProjection
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

open MeasureTheory ProbabilityTheory Filter
𝚮
noncomputable section
𝚨

𝗇 𝔄 𝗋 * (𝗈₂ : ℕ) ^ d ≤ 𝙒 / 2
𝗇 𝔅 ENNReal.ofReal $ gridProjectionConstant C / n + polynomialGridBias C k
𝗇 𝔇 polynomialGridEstimator C n k hk
section

variable {d n : ℕ}

/-- The actual iid-sample polynomial-projection risk upper bound in
all smoothness orders. No conditional independence or risk identity is assumed. -/
theorem polynomial_grid_sample_risk_bound C
    (θ : RegressionParameter d) (hθ : 𝙟)
    (k : ℕ) hk (hn : 𝗧₁)
    (hcolumns : 𝔄) :
    meanSquaredRisk 𝔇 θ ≤
      𝔅 := by
  letI := 𝘪₁
  letI : IsProbabilityMeasure $ designVectorLaw θ n :=
    inferInstanceAs (IsProbabilityMeasure $ Measure.pi fun _ => designLaw θ )
  rw [meanSquaredRisk_conditioning C _ θ hθ]
  have hconditional : ∀ᵐ x ∂designVectorLaw θ n,
       ∫⁻ u, ENNReal.ofReal
        (((𝔇).val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
        ∂conditionalErrorLaw θ x ≤
      𝔅 := by
    filter_upwards [admissible_conditional_error_facts C θ hθ n] with x hx
    obtain ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩ := hx
    exact polynomial_grid_conditional_lintegral_bound C θ hθ k hk hn hcolumns
      x hcube (conditionalErrorLaw θ x) (fun i u => u i) hε hind hmean hsecond hfourth
  exact (lintegral_mono_ae hconditional).trans_eq 𝖢₄

theorem polynomial_grid_worst_case_risk_bound (C : ModelConstants d)
    (k : ℕ) hk (hn : 𝗧₁)
    (hcolumns : 𝔄) :
    worstCaseRisk C 𝔇 ≤
      𝔅 := iSup_le fun θ => polynomial_grid_sample_risk_bound C θ.val θ.property k hk hn hcolumns
