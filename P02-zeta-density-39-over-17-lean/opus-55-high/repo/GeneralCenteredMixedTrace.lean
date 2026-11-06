module
public import GeneralCenteredTrace
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The mixed trace for the actual centered matrix has the required L^2
scale. No moment, reflection, Schur, or matrix-norm estimate is assumed. -/
theorem centered_mixed_trace_general (w : MathCollab.Density.ReflectionCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffContinuousMatrix w L W*cutoffCenteredMatrix w L W*
        cutoffCenteredMatrix w L W)‖ ≤ C*T^η*L*adjacentCenteredBudget K T L W.card := by
  pm_2777 centered_energy_general
  intro T t₀ L hT hL W hW hsep
  pm_2776
  calc
    _ ≤ (B*L)*(∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2) := hh
    _ ≤ (B*L)*(C*T^η*adjacentCenteredBudget K T L W.card) := by
      apply mul_le_mul_of_nonneg_left (hbound T t₀ L hT hL W hW hsep) (by positivity)
    _ = (B*C)*T^η*L*adjacentCenteredBudget K T L W.card := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (adjacentCenteredBudget_nonneg K (by linarith) hLp (Nat.cast_nonneg _))
      gcongr
      linarith

end Montgomery.RationalMoment
