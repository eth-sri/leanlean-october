module

public import NearlyMinimax.ProjectionStatisticalTransfer
public import NearlyMinimax.PolynomialProjectionRates

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

variable {d n : ℕ} (C : ModelConstants d)

/-- A single finite model constant for all sample sizes, including the
small-sample fallback. -/
def projectionUpperConstant : ℝ :=
  gridProjectionConstant C + polynomialProjectionApproximationConstant C +
    2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2

theorem polynomialProjectionApproximationConstant_nonneg :
    0 ≤ polynomialProjectionApproximationConstant C := by
  unfold polynomialProjectionApproximationConstant
  positivity

theorem projectionUpperConstant_nonneg :
    0 ≤ projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  unfold projectionUpperConstant
  positivity

theorem projection_upper_constant_bounds :
    gridProjectionConstant C ≤ projectionUpperConstant C ∧
    polynomialProjectionApproximationConstant C ≤ projectionUpperConstant C ∧
    2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2 ≤
      projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  have hf : 0 ≤ 2 * (polynomialFeatureCount C) * (C.varianceUpper - C.varianceLower) ^ 2 := by positivity
  grind [projectionUpperConstant]

/-- Explicit Borel estimator: the polynomial grid when its feature budget
fits, and the admissible lower variance endpoint for smaller samples. -/
def projectionUpperEstimator (n : ℕ) : Estimator d n :=
  if hn : 2 * polynomialFeatureCount C ≤ n then
    polynomialGridEstimator C n
      (polynomial_projection_grid_size_spec hn).1
  else constantEstimator d n C.varianceLower

/-- Uniform worst-case risk of the constructed estimator, against the
original iid model, in every smoothness order and every positive sample size. -/
theorem projection_upper_estimator_risk (hn : 0 < n) :
    worstCaseRisk C (projectionUpperEstimator C n) ≤
      ENNReal.ofReal (projectionUpperConstant C *
        (1 / n + n ^ (-(4 * C.smoothness / d)))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hbounds := projection_upper_constant_bounds C
  have hK := projectionUpperConstant_nonneg C
  by_cases hbudget : 2 * polynomialFeatureCount C ≤ n
  · rw [projectionUpperEstimator, dite_eq_left hbudget]
    have hspec := polynomial_projection_grid_size_spec hbudget
    apply (polynomial_grid_worst_case_risk_bound hspec.1 hn hspec.2.1).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ _ := add_le_add le_rfl (polynomial_projection_grid_bias_rate hbudget)
      _ ≤ projectionUpperConstant C / n + projectionUpperConstant C *
          n ^ (-(4 * C.smoothness / d)) :=
        by bound
      _ = _ := by ring
  · rw [projectionUpperEstimator, dite_eq_right hbudget]
    apply iSup_le
    intro θ
    apply (constantEstimator_risk_bound C θ.val θ.property).trans
    apply ENNReal.ofReal_le_ofReal
    have hsmall : (n : ℝ) ≤ 2 * polynomialFeatureCount C := by
      exact_mod_cast (by omega)
    have hdiam : (C.varianceUpper - C.varianceLower) ^ 2 ≤ projectionUpperConstant C / n := by
      apply (le_div_iff₀ hnreal).mpr
      nlinarith
    have hrate : 0 ≤ (n : ℝ) ^ (-(4 * C.smoothness / d)) := Real.rpow_nonneg hnreal.le _
    exact hdiam.trans (by rw [div_eq_mul_inv, one_div]; nlinarith [mul_nonneg hK hrate])

/-- The projection upper bound in the paper's root mean square scale,
with the maximum of parametric and smoothness contributions. -/
theorem minimax_rms_projection_upper (hn : 0 < n) :
    minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
      max ((n : ℝ) ^ (-(1 / 2 : ℝ))) (n ^ (-(2 * C.smoothness / d)))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hK := projectionUpperConstant_nonneg C
  let a := (n : ℝ) ^ (-(1 / 2 : ℝ))
  let b := (n : ℝ) ^ (-(2 * C.smoothness / d))
  let m := max a b
  have ha0 : 0 ≤ a := Real.rpow_nonneg hnreal.le _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hnreal.le _
  have hm0  := ha0.trans (le_max_left a b)
  have ha : a ^ 2 = 1 / n := by
    rw [← Real.rpow_mul_natCast hnreal.le]
    norm_num
    simp [Real.rpow_neg_one]
  have hb : b ^ 2 = n ^ (-(4 * C.smoothness / d)) := by
    rw [← Real.rpow_mul_natCast hnreal.le]
    ring
  have ham  := (sq_le_sq₀ ha0 hm0).mpr (le_max_left a b)
  have hbm  := (sq_le_sq₀ hb0 hm0).mpr (le_max_right a b)
  have hreal : projectionUpperConstant C *
      (1 / n + n ^ (-(4 * C.smoothness / d))) ≤
      2 * projectionUpperConstant C * m ^ 2 := by
    nlinarith
  apply (ENNReal.rpow_le_rpow (((minimaxRisk_le_worstCaseRisk C _).trans (projection_upper_estimator_risk C hn)).trans (ENNReal.ofReal_le_ofReal hreal)) (by norm_num)).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hm0]

theorem minimax_rms_projection_parametric_upper {C : ModelConstants d}
    (hn : 0 < n) (hparametric : d ≤ 4 * C.smoothness) :
    minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
      n ^ (-(1 / 2 : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(2 * C.smoothness / d) ≤ -(1 / 2) := by
    apply neg_le_neg
    apply (le_div_iff₀ (by exact_mod_cast C.dimension_pos)).mpr
    nlinarith [hparametric]
  simpa only [max_eq_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp)] using minimax_rms_projection_upper C hn

end NearlyMinimax
