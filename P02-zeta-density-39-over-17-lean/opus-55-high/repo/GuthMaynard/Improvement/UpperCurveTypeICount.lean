module
public import GuthMaynard.Improvement.ShortPoweredDetectorFamily
public import GuthMaynard.Improvement.UpperCurveLargeValues
public import GuthMaynard.Improvement.RealIntegerSource
public import MathCollab.Density.ZeroSeparation
public import GuthMaynard.Improvement.UpperTypeICount
import WeylPort.Analytic.RealLaplace

public section

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option maxRecDepth 2000
namespace GuthMaynard.Improvement

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
/-- Actual upper-window Type-I count, with fixed powering exponent 3/4.
The constant and threshold precede sigma, translation and the zero family. -/
theorem upper_curve_typeI_separated_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ t₀ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) := by pf_10 upper_curve_large_values 9 4

/-- The Type-I branch count on actual zero-slab representatives. -/
theorem upper_curve_typeI_zero_slab_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) := by pm_4571 upper_curve_typeI_separated_count
end

end GuthMaynard.Improvement
