module
public import GuthMaynard.Improvement.ShortDensityConditional
public import GuthMaynard.Improvement.ShortDensityUniform

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Explicit classical input on the actual multiplicity count. Constants may
 depend on sigma and epsilon; this definition asserts no proof of Ingham. -/
def InghamLowerDensity : Prop :=
  ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 9/13 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(2-σ)+ε)

/-- Exact coefficient comparisons covering the entire critical half-strip. -/
theorem global_density_coefficient_comparisons {σ : ℝ} :
    (1/2 ≤ σ → σ ≤ 9/13 → 3*(1-σ)/(2-σ) ≤ (39/17)*(1-σ)) ∧
    (9/13 ≤ σ → σ ≤ 5/7 → 18*(1-σ)/(7*σ+3) ≤ (39/17)*(1-σ)) ∧
    (5/7 ≤ σ → σ ≤ 1 → 15*(1-σ)/(3+5*σ) ≤ (39/17)*(1-σ)) := by
  constructor
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 2-σ)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ 9/13-σ by linarith)]
  constructor
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 7*σ+3)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ σ-9/13 by linarith)]
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 3+5*σ)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ σ-5/7 by linarith)]

