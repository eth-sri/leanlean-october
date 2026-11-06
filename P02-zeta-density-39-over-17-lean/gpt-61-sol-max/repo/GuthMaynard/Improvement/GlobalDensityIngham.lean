module
public import RefinedDensity
public import GuthMaynard.Improvement.GlobalDensityConditional
public import MathCollab.Density.Stronger.NativeDensity

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

private theorem weaken {σ p q : ℝ} (h : ZetaBound σ p) (hpq : p ≤ q) : ZetaBound σ q := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun T hT => (h T hT).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) hpq) hC.le

/-- The padded middle-range estimate closes the interval through sigma=3/4;
above it the preserved, verified density theorem removes any upper-GM premise.
Only the lower Ingham input remains. -/
theorem global_density_fixed_sigma_of_ingham
    (hingham : InghamLowerDensity)
    {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  by_cases hlow : σ ≤ 9/13
  · apply weaken (hingham σ hσ hlow ε hε)
    linarith [(global_density_coefficient_comparisons (σ:=σ)).1 hσ hlow]
  by_cases hmid : σ ≤ 5/7
  · apply weaken (short_density (by linarith) hmid hε)
    linarith [(global_density_coefficient_comparisons (σ:=σ)).2.1 (by linarith) hmid]
  by_cases hupper : σ ≤ 3/4
  · apply weaken (Montgomery.Refined.refined_density_middle (by linarith) hupper hε)
    refine add_le_add ?_ le_rfl
    apply (div_le_iff₀ (by linarith : 0 < 7*σ+3)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ σ-5/7 by linarith)]
  · apply weaken (Stronger.stronger_density_bound_native (lt_of_not_ge hupper) hε)
    have hd : 0 < 2*σ := by linarith
    have hc : (3:ℝ)/(2*σ) ≤ 39/17 := (div_le_iff₀ hd).mpr (by linarith)
    convert add_le_add_right (mul_le_mul_of_nonneg_right hc (show 0 ≤ 1-σ by linarith)) ε using 1 <;> ring

/-- Actual global39/17, uniform in sigma, with no published upper-GM input.
The lower Ingham premise remains explicit and unasserted here. -/
theorem global_density_uniform_of_ingham
    (hingham : InghamLowerDensity)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  apply zetaDensityCount_uniform_of_fixed_sigma (show (0:ℝ)<39/17 by norm_num) _ hε
  intro σ hσ hσ' ε hε
  exact global_density_fixed_sigma_of_ingham hingham hσ hσ' hε

end GuthMaynard.Improvement
