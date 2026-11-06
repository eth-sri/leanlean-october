module
public import TraceAlternatives.UniversalShellBudget
public import DensityEnergyGM.DifferenceEnergyGeometry
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The original ordered energy absorbs quadratic near and shell errors. -/
theorem card_sq_le_twice_universalCenteredBudget {T t₀ L : ℝ}
    (hT : 2 ≤ T) (hL : 0 ≤ L) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) :
    (W.card : ℝ)^2 ≤ 2*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  pm_2730
  have hOther : 0≤T^(1/2:ℝ)*L^(1/2:ℝ)*(W.card:ℝ)^2+
      T^(1/2:ℝ)*L^(2/3:ℝ)*(W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)+
      T^(9/16:ℝ)*L^(1/2:ℝ)*(W.card:ℝ)^(19/12:ℝ)*(discreteAdditiveEnergy W:ℝ)^(5/48:ℝ) := by positivity
  unfold universalCenteredBudget
  grind


theorem centered_shell_universal (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      2 ≤ T → Real.sqrt T ≤ L → 0 < H → H ≤ 2*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)+
          B*(W.card:ℝ)^2*L^(2-2*(A:ℝ)) := by pm_2731 reflection_local_energy_universal universal_shell_budget_le universalCenteredBudget universalLocalReflectionBudget universalCenteredBudget_nonneg

end Montgomery.RationalMoment
