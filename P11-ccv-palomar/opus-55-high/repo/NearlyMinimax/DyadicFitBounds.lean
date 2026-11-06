module

public import NearlyMinimax.DyadicTaylor
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The original population increment and spatial approximation bounds in U2. -/

𝛍
𝚺
𝚨

𝗇 𝔅 M ^ s
theorem bounded_rpow_le_linear (r M s : ℝ) (hr : 𝘵₁) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 𝔅 * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      $ by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 𝔅) hr
  · calc
      r ^ s ≤ 𝔅 := Real.rpow_le_rpow hr hrM $ zero_le_one.trans hs
      _ ≤ 𝔅 * r := 𝖥₄
      _ ≤ max 1 𝔅 * r := mul_le_mul_of_nonneg_right (le_max_right ..) hr

𝗇 𝔄 (EuclideanSpace.equiv 𝗎 ℝ).symm
𝗇 𝔈 𝗰₂
𝗇 𝔊 ‖𝔄 (𝔈 *ᵥ c)‖
theorem anchoredTransport_euclidean_norm c :
    𝔊 ≤
      𝙖 * ‖𝔄 c‖ := by
  have h := Matrix.l2_opNorm_mulVec 𝔈
    $ 𝔄 c
  have h' : 𝔊 ≤
      ‖𝔈‖ * ‖𝔄 c‖ := by
    assumption
  apply h'.trans
  exact mul_le_mul_of_nonneg_right (anchoredTransport_norm_le_half d ℓ) $ norm_nonneg _

𝗇 𝔉 fun j => dyadicPopulationFit θ j x
def dyadicPopulationIncrement (θ : RegressionParameter d) (x : Covariate d) :
    ℕ → 𝗎 → ℝ := anchoredIncrement 𝔉

𝗇 𝔇 𝘑₁
theorem dyadicPopulationIncrement_error_identity θ
    x c j :
    dyadicPopulationIncrement θ x 𝔇 =
       dyadicPopulationFit θ 𝔇 x - dyadicTaylorCoefficients c 𝔇 -
        𝔈 *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j) := by
  rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]
  aesop

theorem dyadic_inverse_scale_succ j :
    𝗜⁻¹ = 2 * (𝙉 ^ 𝔇)⁻¹ := by
  ring

theorem dyadicPopulationIncrement_telescope θ
    (x z : Covariate d) J :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range 𝗯, 𝘧₁ ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope 𝔉 x z J).symm
