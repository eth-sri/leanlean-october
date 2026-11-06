module
public import TraceAlternatives.UniversalCenteredShell
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory
namespace Montgomery.RationalMoment

section
variable (w : MathCollab.Density.ReflectionCutoff) {η : ℝ} (hη : 0 < η)
include w η hη
/-- The sharp second moment reflected through every shell of the actual
centered cutoff kernel, with the original ordered energy. -/
theorem centered_energy_universal :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by pm_4085 centered_shell_universal universalCenteredBudget universalCenteredBudget_nonneg card_sq_le_twice_universalCenteredBudget

/-- The actual squared-cutoff centered matrix satisfies the improved
quadratic trace bound, with no analytic estimate among the premises. -/
theorem centered_trace_universal :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W)‖ ≤
        C*T^η*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by pm_2733 centered_energy_universal
end

end Montgomery.RationalMoment
