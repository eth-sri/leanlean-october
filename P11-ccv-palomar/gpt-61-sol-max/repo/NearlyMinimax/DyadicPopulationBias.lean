module

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

theorem anchoredFinVector_dotProduct {d ℓ } (u v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector u ⬝ᵥ anchoredFinVector v = u ⬝ᵥ v := by
  simp only [dotProduct, anchoredFinVector, anchoredFinIndex]
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ : AnchoredIndex d ℓ => u γ * v γ)

theorem dyadicPilotRow_dot_coefficients {d ℓ } j
    x y (v : AnchoredIndex d ℓ → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  anchoredFinVector_dotProduct _ _

theorem finite_row_abs_dot_le_euclidean_norm {ι : Type*} [Fintype ι]
    (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using
        PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm v) i
    _ = _ := by rw [Finset.sum_mul]

theorem dyadic_scale_rpow_cancel j (s : ℝ) :
    2 ^ j * (((2 : ℝ) ^ j)⁻¹) ^ s = ((2 ^ j)⁻¹) ^ (s - 1) := by
  have h := positive_rpow_times_distance (((2 : ℝ) ^ j)⁻¹) s ((2 : ℝ) ^ j) (by positivity)
  simp_all [mul_comm]

section
variable {d : ℕ} (C : ModelConstants d)
include C

def dyadicPopulationPolynomial  θ
    j x y m  :=
  incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m (dyadicIncrementRawMean θ j x)

def dyadicPopulationBiasBudget  J (m : ℕ → ℕ)  :=
  (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
    ∑ j ∈ Finset.range (J + 1), (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
      ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C)

def dyadicPopulationResidual  θ
    J (m : ℕ → ℕ) x y  :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)
end


end NearlyMinimax
