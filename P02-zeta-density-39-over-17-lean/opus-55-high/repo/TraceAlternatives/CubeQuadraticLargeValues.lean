module
public import QuadraticAmplifiedMoment
public import TraceAlternatives.CubeCenteredTrace
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The actual quadratic amplifier with the sharp reflected trace.
Every analytic input is supplied, with the original closed ordered energy. -/
theorem finite_quadratic_large_value_cube (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → Real.sqrt T ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        (N^3/L)*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W)) := by pm_2734 centered_trace_cube cubeCenteredBudget_nonneg cubeCenteredBudget

/-- Mixed trace16 in the actual quadratic large-value inequality, with
all analytic estimates supplied and every original height/length range. -/
theorem finite_quadratic_large_value_cube_native
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → Real.sqrt T ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        N^3*T/L*(W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ)+
        N^3*T^(1/3:ℝ)*(W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ)) := by
  pm_8728 finite_quadratic_large_value_cube
  pm_2735
  exact h.trans_eq (by unfold cubeCenteredBudget; field_simp; ring)

end Montgomery.RationalMoment
