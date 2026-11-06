module
public import TraceAlternatives.UniversalCenteredShell
public import DensityEnergyGM.SharpCenteredTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

theorem centered_energy_universal (w : MathCollab.Density.ReflectionCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) :=
  centered_energy_of_shell universalCenteredBudget
    (fun hT hL hR hE => universalCenteredBudget_nonneg hT hL hR hE)
    (fun hT hL W hW => card_sq_le_twice_universalCenteredBudget hT hL W hW)
    (fun w {η} hη => centered_shell_universal w (A := 2) (by norm_num) hη) w hη

theorem centered_trace_universal (w : MathCollab.Density.ReflectionCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 2 ≤ T → Real.sqrt T ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W)‖ ≤
        C*T^η*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hbound⟩ := centered_energy_universal (reflectionSquare w) hη
  refine ⟨C,hC,?_⟩
  intro T t₀ L hT hLs W hW hsep
  rw [cutoff_centered_trace_identity,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)))]
  exact hbound T t₀ L hT hLs W hW hsep

end Montgomery.RationalMoment
