module

public import NearlyMinimax.GridProjectionRisk
public import NearlyMinimax.Risk

@[expose] public section


open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace NearlyMinimax

variable {d : ℕ} (C : ModelConstants d)

/-- A uniform stochastic constant depending only on the fixed model. -/
def gridProjectionConstant (C : ModelConstants d) : ℝ :=
  4 * max C.fourthBound (2 * C.varianceUpper ^ 2) +
    32 * C.varianceUpper * C.holderBound ^ 2

theorem gridProjectionConstant_nonneg (C : ModelConstants d) :
    0 ≤ gridProjectionConstant C := by
  have hV := C.varianceLower_pos.trans C.variance_interval
  have hm : 0 ≤ max C.fourthBound (2 * C.varianceUpper ^ 2) :=
    (by positivity : 0 ≤ 2 * C.varianceUpper ^ 2).trans (le_max_right _ _)
  unfold gridProjectionConstant
  positivity

/-- The variance-specific conditional constant is bounded by the model
constant, using the actual admissible variance interval. -/
theorem admissible_grid_projection_constant_bound 
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    4 * max C.fourthBound (2 * θ.variance ^ 2) +
      32 * θ.variance * C.holderBound ^ 2 ≤ gridProjectionConstant C := by
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hV := hθ.2.2.2.2.2.2.1
  have hm := max_le_max_left C.fourthBound (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hV0 (hV0.trans hV)).mpr hV) (by norm_num : (0 : ℝ) ≤ 2))
  have hlinear := mul_le_mul_of_nonneg_right hV (by positivity : 0 ≤ 32 * C.holderBound ^ 2)
  unfold gridProjectionConstant
  nlinarith

end NearlyMinimax
