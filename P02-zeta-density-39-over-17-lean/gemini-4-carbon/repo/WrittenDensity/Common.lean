module
public import ZeroFreeDensityBridge
public import GuthMaynard.Improvement.CurveUniformization

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density

def DensityBound (σ p ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T : ℝ) ≤ C * T ^ (p + ε)

theorem density_weaken {σ p q ε : ℝ} (h : DensityBound σ p ε)
    (hpq : p ≤ q) : DensityBound σ q ε :=
  let ⟨C, hC, hb⟩ := h
  ⟨C, hC, fun T hT => (hb T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)⟩

theorem weaken_frac {σ a₁ b₁ a₂ b₂ ε : ℝ}
    (h : DensityBound σ (a₁ * (1 - σ) / b₁) ε)
    (hσ : σ ≤ 1 := by linarith) (hb₁ : 0 < b₁ := by linarith)
    (hb₂ : 0 < b₂ := by linarith) (hle : a₁ * b₂ ≤ a₂ * b₁ := by linarith) :
    DensityBound σ ((a₂ / b₂) * (1 - σ)) ε := by
  refine density_weaken h ?_
  rw [← div_mul_eq_mul_div]
  exact mul_le_mul_of_nonneg_right ((div_le_div_iff₀ hb₁ hb₂).2 hle) (by linarith)

theorem density_of_actual_zero {σ p ε : ℝ} (hσ : 7/8 < σ) :
    DensityBound σ p ε := by
  refine ⟨1, zero_lt_one, fun T _ => ?_⟩
  rw [Montgomery.ZeroFreeHatching.actual_density_count_zero hσ, Nat.cast_zero]
  positivity

end Montgomery.WrittenDensity
