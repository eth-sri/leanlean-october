module
public import GuthMaynard.Improvement.ShortLocalZeroCount

@[expose] public section
open Complex Filter Set MeasureTheory
open scoped Topology BigOperators
open MathCollab.Density.ZetaGrowth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

theorem zeta_unit_bin_sum_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 7 / 10 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        zetaMultiplicity ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7/4 : ℝ) / (3/2 : ℝ)) :=
  GuthMaynard.Improvement.short_zeta_unit_bin_sum_le_jensen σ T z (by linarith) hT

/-- A single logarithmic multiplicity constant for every actual zero bin. -/
theorem zeta_local_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 3/4 ≤ σ → 2 ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ C*Real.log (2*T) := by
  obtain ⟨C, hC, h⟩ := GuthMaynard.Improvement.short_zeta_local_multiplicity_bound
  exact ⟨C, hC, fun σ T hσ hT k => h σ T (by linarith) hT k⟩

end MathCollab.Density
