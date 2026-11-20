module

public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Actual coordinatewise chart bounds for the finite polynomial frame. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d n F : ℕ} {C η ρ : ℝ} (hC : 1 ≤ C) {x : Covariate d} (hx : ∀ i, |x i| ≤ 2)

include hx in
theorem highFrameFeature_abs_le_one (γ : HighFrameIndex d F) :
    |highFrameFeature x γ| ≤ 1 := by
  unfold highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_pow]
    have hb : |x i / 8| ≤ 1 := by
      rw [abs_div]
      rw [show |(8 : ℝ)| = 8 by norm_num]
      apply (div_le_one (by norm_num)).mpr
      exact (hx i).trans (by norm_num)
    exact pow_le_one₀ (abs_nonneg _) hb

include hx in
theorem highFrameProfile_abs_le_coefficients (v : HighFrameVector d F) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ ∑ γ, |v γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highFrameFeature_abs_le_one hx γ) (abs_nonneg _)).trans_eq (one_mul _)

include hC hx in
theorem highFrameProfile_abs_le_one {v : HighFrameVector d F}
    (hv : ∑ γ, |v γ| ≤ C⁻¹) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ 1 :=
  (highFrameProfile_abs_le_coefficients hx v).trans (hv.trans (inv_le_one_of_one_le₀ hC))

include hC in
theorem highFrameCoefficientRegression_abs_le (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2)
    {g w : Fin n → ℝ} (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    {c : HighFrameVector d F} (hc : ∑ γ, |c γ| ≤ C⁻¹) (i : Fin n) :
    |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ :=
  coefficientRegression_abs_le hη hηρ (hg i) (hw i) (highFrameProfile_abs_le_one hC (hU i) hc)

end NearlyMinimax
