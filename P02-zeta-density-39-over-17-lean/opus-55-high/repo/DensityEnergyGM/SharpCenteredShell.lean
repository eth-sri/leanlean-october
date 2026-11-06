module
public import DensityEnergyGM.SharpShellBudget
public import DensityEnergyGM.DifferenceEnergyGeometry
public import TraceAlternatives.CubeCenteredShell
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The original ordered energy absorbs quadratic near and shell errors. -/
theorem card_sq_le_twice_sharpCenteredBudget {T t₀ L : ℝ}
    (hT : 2 ≤ T) (hL : 0 ≤ L) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) :
    (W.card : ℝ)^2 ≤ 2*sharpCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  pm_2730
  have hOther : 0 ≤ T^(4/5:ℝ)*L^(1/5:ℝ)*(W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)+
      T^(9/20:ℝ)*L^(4/5:ℝ)*(W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ) := by positivity
  unfold sharpCenteredBudget
  linarith

theorem centered_shell_sharp (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      2 ≤ T → Real.sqrt T ≤ L → 0 < H → H ≤ 2*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*sharpCenteredBudget T L W.card (discreteAdditiveEnergy W)+
          B*(W.card:ℝ)^2*L^(2-2*(A:ℝ)) := by pm_2731 reflection_local_energy_sharp sharp_shell_budget_le sharpCenteredBudget sharpLocalReflectionBudget sharpCenteredBudget_nonneg

end Montgomery.RationalMoment
