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

theorem dyadicIncrementRawMean_eq_with_virtual_parent {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x)
          (if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x))
        (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  unfold dyadicIncrementPopulation
  rw [dyadicFinPilotGram_eq_normalized C θ hθ j x]
  by_cases hj : j = 0
  · simp [hj, anchoredFinNormalizedGram_one]
  · simp only [hj, ite_false]
    rw [dyadicFinPilotGram_eq_normalized C θ hθ (j - 1) x]

def dyadicPopulationRawPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinRawVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) t m (dyadicIncrementRawMean θ j x)

theorem dyadicPopulationPolynomial_affine {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m := by
  exact congrFun (incrementFinVector_affine _ _ _ _ y m) (dyadicIncrementRawMean θ j x)

end NearlyMinimax
