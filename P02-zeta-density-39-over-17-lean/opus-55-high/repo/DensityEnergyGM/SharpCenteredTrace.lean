module
public import DensityEnergyGM.SharpCenteredShell
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory
namespace Montgomery.RationalMoment

section
variable (w : MathCollab.Density.ReflectionCutoff) {η : ℝ} (hη : 0 < η)
include w η hη
/-- The sharp second moment reflected through every shell of the actual
centered cutoff kernel, with the original ordered energy. -/
theorem centered_energy_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*sharpCenteredBudget T L W.card (discreteAdditiveEnergy W) := by pm_4085 centered_shell_sharp sharpCenteredBudget sharpCenteredBudget_nonneg card_sq_le_twice_sharpCenteredBudget

/-- The actual squared-cutoff centered matrix satisfies the improved
quadratic trace bound, with no analytic estimate among the premises. -/
theorem centered_trace_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W)‖ ≤
        C*T^η*sharpCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hbound⟩ := centered_energy_sharp (reflectionSquare w) hη
  pm_417 hLs
end

end Montgomery.RationalMoment
