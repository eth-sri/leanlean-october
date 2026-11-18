module
public import MathCollab.Density.ZetaCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def InghamLowerDensity : Prop :=
  ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 9/13 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(2-σ)+ε)

end GuthMaynard.Improvement
