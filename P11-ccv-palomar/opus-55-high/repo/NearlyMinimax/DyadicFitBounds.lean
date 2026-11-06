module

public import NearlyMinimax.DyadicTaylor

@[expose] public section

/-! The original population increment and spatial approximation bounds in U2. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem bounded_rpow_le_linear (r M s : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 (M ^ s) * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (M ^ s)) hr)
  · have h1r : 1 ≤ r := (le_of_not_ge hr1)
    calc
      r ^ s ≤ M ^ s := Real.rpow_le_rpow hr hrM (zero_le_one.trans hs)
      _ ≤ M ^ s * r := by simpa using mul_le_mul_of_nonneg_left h1r (Real.rpow_nonneg (hr.trans hrM) s)
      _ ≤ max 1 (M ^ s) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr

theorem anchoredTransport_euclidean_norm {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      (1 / 2) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
  have h := Matrix.l2_opNorm_mulVec (anchoredTransport d ℓ)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c)
  have h' : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      ‖anchoredTransport d ℓ‖ * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
    simpa [EuclideanSpace.equiv] using h
  apply h'.trans
  exact mul_le_mul_of_nonneg_right (anchoredTransport_norm_le_half d ℓ) (norm_nonneg _)

def dyadicPopulationIncrement {d ℓ : ℕ} (θ : RegressionParameter d) (x : Covariate d) :
    ℕ → AnchoredIndex d ℓ → ℝ := anchoredIncrement (fun j => dyadicPopulationFit θ j x)

theorem dyadicPopulationIncrement_error_identity {d ℓ : ℕ} (θ : RegressionParameter d)
    (x : Covariate d) (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    dyadicPopulationIncrement θ x (j + 1) =
      (dyadicPopulationFit θ (j + 1) x - dyadicTaylorCoefficients c (j + 1)) -
        anchoredTransport d ℓ *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j) := by
  rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]
  unfold dyadicPopulationIncrement anchoredIncrement
  abel

theorem dyadic_inverse_scale_succ (j : ℕ) :
    ((2 : ℝ) ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by
  rw [pow_succ]
  field_simp

theorem dyadicPopulationIncrement_telescope {d ℓ : ℕ} (θ : RegressionParameter d)
    (x z : Covariate d) (J : ℕ) :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope (fun j => dyadicPopulationFit θ j x) x z J).symm

end NearlyMinimax
