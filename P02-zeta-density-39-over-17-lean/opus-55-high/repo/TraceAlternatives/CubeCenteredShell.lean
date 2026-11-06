module
public import TraceAlternatives.CubeShellBudget
public import DensityEnergyGM.DifferenceEnergyGeometry
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The original ordered energy absorbs quadratic near and shell errors. -/
theorem card_sq_le_twice_cubeCenteredBudget {T t₀ L : ℝ}
    (hT : 2 ≤ T) (hL : 0 ≤ L) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) :
    (W.card : ℝ)^2 ≤ 2*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  pm_2730
  have hEupper : (discreteAdditiveEnergy W:ℝ) ≤ (W.card:ℝ)^4 := by
    pm_6377 hh
    exact_mod_cast hh
  have hSixth : (discreteAdditiveEnergy W:ℝ)^(1/6:ℝ) ≤ (W.card:ℝ)^(2/3:ℝ) := by
    have hh := Real.rpow_le_rpow hEn hEupper (by norm_num : (0:ℝ)≤1/6)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg W.card)] at hh
    norm_num at hh
    exact hh
  have hRoot : (discreteAdditiveEnergy W:ℝ)^(1/2:ℝ) ≤
      (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by
    by_cases hz : (discreteAdditiveEnergy W:ℝ)=0
    simp_all
    have hp : 0 < (discreteAdditiveEnergy W:ℝ) := lt_of_le_of_ne hEn (Ne.symm hz)
    have hh := mul_le_mul_of_nonneg_right hSixth
      (Real.rpow_nonneg hEn (1/3:ℝ))
    rw [← Real.rpow_add hp] at hh
    norm_num at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hRoot (show 0≤2*T by positivity)
  have hOther : 0 ≤ L*T^(1/3:ℝ)*(W.card:ℝ)^(2/3:ℝ)*
      (discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by positivity
  unfold cubeCenteredBudget
  grind


theorem centered_shell_cube (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      2 ≤ T → Real.sqrt T ≤ L → 0 < H → H ≤ 2*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W)+
          B*(W.card:ℝ)^2*L^(2-2*(A:ℝ)) := by pm_2731 reflection_local_energy_cube cube_shell_budget_le cubeCenteredBudget cubeLocalReflectionBudget cubeCenteredBudget_nonneg

end Montgomery.RationalMoment
