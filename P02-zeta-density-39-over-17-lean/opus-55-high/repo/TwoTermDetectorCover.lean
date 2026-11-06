module
public import DensityWindowBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- Uniform logarithmic buffer for the entire compact target exponent range. -/
theorem two_term_power_buffer_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 7/10 ≤ a → a ≤ 4/5 →
      T*(Real.log T)^4 ≤ T^(3*a/2) ∧
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by pf_75 20 21

/-- Actual short detection yields a bounded-coefficient powered family in the
full target window, without moving the ordinate. No counting estimate is assumed. -/
theorem two_term_powered_cover {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 ∧
      ∀ (a σ : ℝ) (ρ : ℂ), 7/10 ≤ a → a ≤ 4/5 →
        0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → 1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ shortPoweredDetectorIndices T,
          T^a ≤ (shortPoweredDetectorScale p:ℝ) ∧
          (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
          2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 ∧
          (shortPoweredDetectorScale p:ℝ)^σ*T^(-2*η) ≤
            ‖detectingPolynomial (shortPoweredDetectorScale p)
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by pm_2714 two_term_power_buffer_eventually



end Montgomery.RationalMoment
