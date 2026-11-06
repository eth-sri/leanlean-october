module

public import NearlyMinimax.GridProjection
public import NearlyMinimax.ProjectionRates
public import NearlyMinimax.Risk
public import RoughRegime.Notation

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace NearlyMinimax

/-- A uniform stochastic constant depending only on the fixed model. -/
def gridProjectionConstant (C : ModelConstants d) : ℝ :=
  4 * max C.fourthBound (2 * C.varianceUpper ^ 2) +
    32 * C.varianceUpper * C.holderBound ^ 2

theorem gridProjectionConstant_nonneg (C : ModelConstants d) :
    0 ≤ gridProjectionConstant C := by
  have hV := C.varianceLower_pos.trans C.variance_interval
  unfold gridProjectionConstant
  positivity

/-- The variance-specific conditional constant is bounded by the model
constant, using the actual admissible variance interval. -/
theorem admissible_grid_projection_constant_bound
    C (θ : RegressionParameter d) (hθ : 𝙟) :
    4 * max C.fourthBound (2 * θ.variance ^ 2) +
      32 * θ.variance * C.holderBound ^ 2 ≤ gridProjectionConstant C := by
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hV := hθ.2.2.2.2.2.2.1
  have hm := max_le_max_left C.fourthBound $ mul_le_mul_of_nonneg_left ((sq_le_sq₀ hV0 $ hV0.trans hV ).mpr hV) (by norm_num : 𝙋 ≤ 2)
  unfold gridProjectionConstant
  nlinarith
