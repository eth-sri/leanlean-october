module
public import GuthMaynard.Improvement.GlobalDensityIngham
public import GuthMaynard.Improvement.NativeIngham

public section

open MathCollab.Density
namespace GuthMaynard.Improvement

/-- Global39/17 for the actual nontrivial zeta-zero count, with analytic
multiplicity and both ordinate signs. One constant precedes sigma and height. -/
theorem global_density_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  exact global_density_uniform_of_ingham ingham_lower_density hε

end GuthMaynard.Improvement
