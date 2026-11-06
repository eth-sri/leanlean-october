module
public import GeneralDetectorCover

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
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by
  filter_upwards [general_power_buffer_eventually] with T hT
  exact fun a ha ha' => hT a (by linarith) ha'

/-- Complete fixed finite powered detector cover for the two-term branch. -/
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
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by
  filter_upwards [general_powered_cover hη] with T hT
  refine ⟨hT.1, ?_⟩
  intro a σ ρ ha ha' hσ hσβ hβ hlarge
  exact hT.2 a σ ρ (by linarith) ha' hσ hσβ hβ hlarge

end Montgomery.RationalMoment
