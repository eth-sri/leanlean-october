module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ProjectionStatistical
public import NearlyMinimax.PolynomialGridProjection

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

variable {d n : ℕ} {C : ModelConstants d}

/-- The actual iid-sample polynomial-projection risk upper bound in
all smoothness orders. No conditional independence or risk identity is assumed. -/
theorem polynomial_grid_sample_risk_bound
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    {k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcolumns : k ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) :
    meanSquaredRisk (polynomialGridEstimator C n hk) θ ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
  letI := designLaw_isProbability C θ hθ
  letI : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ => designLaw θ)))
  rw [meanSquaredRisk_conditioning _ hθ]
  exact (lintegral_mono_ae (by
    filter_upwards [admissible_conditional_error_facts hθ n] with x hx
    obtain ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩ := hx
    apply polynomial_grid_conditional_lintegral_bound <;> assumption)).trans_eq (by simp)

theorem polynomial_grid_worst_case_risk_bound
    {k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcolumns : k ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) :
    worstCaseRisk C (polynomialGridEstimator C n hk) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := iSup_le fun θ => polynomial_grid_sample_risk_bound θ.property hk hn hcolumns

end NearlyMinimax
