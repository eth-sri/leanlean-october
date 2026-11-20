module

public import NearlyMinimax.DyadicTaylor

@[expose] public section

/-! The original population increment and spatial approximation bounds in U2. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem bounded_rpow_le_linear {r M s : ℝ} (hr : 0 ≤ r) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 (M ^ s) * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (M ^ s)) hr)
  · calc
      _ ≤ M ^ s := by bound
      _ ≤ M ^ s * r := by bound
      _ ≤ _ := by bound

variable {d ℓ : ℕ} (θ : RegressionParameter d) (x : Covariate d) (c : AnchoredIndex d ℓ → ℝ)

theorem anchoredTransport_euclidean_norm :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      (1 / 2) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
  have h := Matrix.l2_opNorm_mulVec (anchoredTransport d ℓ)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c)
  have h' : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      ‖anchoredTransport d ℓ‖ * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
    assumption
  apply h'.trans
  bound [anchoredTransport_norm_le_half d ℓ]

def dyadicPopulationIncrement :
    ℕ → AnchoredIndex d ℓ → ℝ := anchoredIncrement (fun j => dyadicPopulationFit θ j x)

theorem dyadic_inverse_scale_succ (j : ℕ) :
    (2 ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by
  rw [pow_succ]
  field_simp

theorem dyadicPopulationIncrement_telescope (z : Covariate d) (J : ℕ) :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope (fun j => dyadicPopulationFit θ j x) x z J).symm

end NearlyMinimax
