module
public import TwoTermLargeValues
public import TwoTermDetectorCover
public import TwoTermWindowParameters
public import ThirdZeroDensity
import WeylPort.Analytic.RealLaplace

public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped Topology
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

section
variable {σ a p α ε : ℝ} (hw : TwoTermWindow σ a p α) (hε : 0 < ε)
include σ a p α ε hw hε
/-- Actual Type-I detection with every powered length covered. -/
theorem two_term_typeI_separated_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (t₀ : ℝ) (R : Finset ℂ),
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by pf_14 two_term_full_window_large_values two_term_powered_cover 7 10

/-- The Type-I branch count on actual zeta zero representatives. -/
theorem two_term_typeI_zero_slab_count :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ R : Finset ℂ,
      R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(p+ε) := by pm_2707 two_term_typeI_separated_count

/-- Actual slabs: the weak Type-II moment is already proved and its exponent
is checked against p. Multiplicity and ordinate collisions are restored. -/
theorem two_term_slab_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(p+ε) := by pm_2708 two_term_typeI_zero_slab_count weak_short_typeII_zero_slab_count

/-- End-to-end theorem for actual riemannZeta zeros. TwoTermWindow contains
only explicit algebraic inequalities; no analytic conclusion is assumed. -/
theorem two_term_density :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  pm_69 C hC hslab two_term_slab_density hw hε
  pm_2709
end

/-- First new unconditional density branch, including both endpoints. -/
theorem two_term_density_first {σ ε : ℝ}
    (hσ : 12/17 ≤ σ) (hσ' : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(8*σ-3)+ε) :=
  two_term_density (two_term_window_first σ hσ hσ') hε

end Montgomery.RationalMoment
