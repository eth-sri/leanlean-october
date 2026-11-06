module
public import ZeroFreeDensityBridge

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Montgomery.WrittenDensity
open MathCollab.Density

/-- Actual zero-free count supplies every real exponent on the strict
right half-plane. This is a count consequence, not the source analytic route. -/
theorem density_of_actual_zero {σ p ε : ℝ} (hσ : (7/8 : ℝ) < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(p+ε) := by
  refine ⟨1,by norm_num,?_⟩
  intro T hT
  rw [Montgomery.ZeroFreeHatching.actual_density_count_zero hσ,Nat.cast_zero]
  positivity

end Montgomery.WrittenDensity
