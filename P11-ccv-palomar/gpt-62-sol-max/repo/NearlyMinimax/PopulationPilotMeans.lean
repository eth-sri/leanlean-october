module

public import NearlyMinimax.DyadicPopulationBias
public import NearlyMinimax.ResponseOperators

@[expose] public section

/-! Actual uniformly bounded multiscale population coefficient fields. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicPopulationRawPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinRawVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) t m (dyadicIncrementRawMean θ j x)

theorem dyadicPopulationPolynomial_affine {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m := congrFun (incrementFinVector_affine _ _ _ _ y m) (dyadicIncrementRawMean θ j x)

end NearlyMinimax
