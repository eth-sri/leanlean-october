module

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.DyadicIncrementBias
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.InverseDerivativeFamily

@[expose] public section

/-! The true finite multiscale population residual in original U8. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d ℓ : ℕ}

theorem anchoredFinVector_dotProduct (u v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector u ⬝ᵥ anchoredFinVector v = u ⬝ᵥ v := by
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
      (fun γ : AnchoredIndex d ℓ => u γ * v γ)

theorem dyadicPilotRow_dot_coefficients (j : ℕ)
    (x y : Covariate d) (v : AnchoredIndex d ℓ → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  anchoredFinVector_dotProduct _ _

end

theorem finite_row_abs_dot_le_euclidean_norm {ι : Type*} [Fintype ι]
    (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
  apply abs_weighted_sum_le
  intro i _
  simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using
    PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm v) i

theorem dyadic_scale_rpow_cancel (j : ℕ) (s : ℝ) :
    (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ s = (((2 : ℝ) ^ j)⁻¹) ^ (s - 1) := by
  have h := positive_rpow_times_distance (((2 : ℝ) ^ j)⁻¹) s ((2 : ℝ) ^ j) (by positivity)
  simpa only [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul, mul_comm] using h

def dyadicPopulationPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m (dyadicIncrementRawMean θ j x)

/-- Degree-dependent part of the inverse-polynomial approximation error. -/
def dyadicPolynomialDecay {d : ℕ} (C : ModelConstants d) (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C)

theorem dyadicPolynomialDecay_nonneg {d : ℕ} (C : ModelConstants d) (m : ℕ) :
    0 ≤ dyadicPolynomialDecay C m := by unfold dyadicPolynomialDecay; positivity

def dyadicPopulationBiasBudget {d : ℕ} (C : ModelConstants d) (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
    ∑ j ∈ Finset.range (J + 1), (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
      dyadicPolynomialDecay C (m j)

def dyadicPopulationResidual {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) : ℝ :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)

end NearlyMinimax
