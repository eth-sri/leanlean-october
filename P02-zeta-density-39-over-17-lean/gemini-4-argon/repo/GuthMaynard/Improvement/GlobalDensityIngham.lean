module
public import GuthMaynard.Improvement.WeakShortDensity
public import GuthMaynard.Improvement.GlobalDensityConditional
public import MathCollab.Density.Stronger.NativeDensity
public import ThirdZeroDensity

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem global_density_fixed_sigma_of_ingham
    (hingham : InghamLowerDensity)
    {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  have h1 : 0 ≤ 1 - σ := by linarith
  by_cases hlow : σ ≤ 9/13
  · obtain ⟨C,hC,hbound⟩ := hingham σ hσ hlow ε hε
    refine ⟨C,hC,fun T hT => (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).1 hσ hlow])) hC.le)⟩
  by_cases hmid : σ ≤ 5/7
  · obtain ⟨C,hC,hbound⟩ := short_density (le_of_not_ge hlow) hmid hε
    refine ⟨C,hC,fun T hT => (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).2.1 (le_of_not_ge hlow) hmid])) hC.le)⟩
  by_cases h2 : σ ≤ 113/153
  · obtain ⟨C,hC,hbound⟩ := Montgomery.RationalMoment.adjacent_density_second (le_of_not_ge hmid) h2 hε
    have hd : 0 < 9*σ - 1 := by linarith
    have hA : 12*(1-σ)/(9*σ-1) ≤ (39/17)*(1-σ) := by
      rw [div_le_iff₀ hd]; nlinarith
    refine ⟨C,hC,fun T hT => (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)⟩
  by_cases hupper : σ ≤ 3/4
  · obtain ⟨C,hC,hbound⟩ := Montgomery.RationalMoment.third_density_segment (le_of_not_ge h2) hupper hε
    have hd : 0 < 153*σ + 7 := by linarith
    have hA : 255*(1-σ)/(153*σ+7) ≤ (39/17)*(1-σ) := by
      rw [div_le_iff₀ hd]; nlinarith
    refine ⟨C,hC,fun T hT => (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)⟩
  · obtain ⟨C,hC,hbound⟩ := MathCollab.Density.Stronger.stronger_density_bound_native (lt_of_not_ge hupper) hε
    have hd : 0 < 2*σ := by linarith
    have hA : 3*(1-σ)/(2*σ) ≤ (39/17)*(1-σ) := by
      rw [div_le_iff₀ hd]; nlinarith
    refine ⟨C,hC,fun T hT => (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)⟩

theorem global_density_uniform_of_ingham
    (hingham : InghamLowerDensity)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  apply zetaDensityCount_uniform_of_fixed_sigma (show (0:ℝ)<39/17 by norm_num) _ hε
  intro σ hσ hσ' ε hε
  exact global_density_fixed_sigma_of_ingham hingham hσ hσ' hε

