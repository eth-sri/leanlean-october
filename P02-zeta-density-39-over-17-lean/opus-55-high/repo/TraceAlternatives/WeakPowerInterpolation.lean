module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- The minimum is below every geometric interpolation of two nonnegative
bounds. Zero bases are retained explicitly. -/
theorem min_le_geometric_power {A D θ : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min A D ≤ A^(1-θ)*D^θ := by
  by_cases hAz : A=0
  · rw [hAz,min_eq_left hD]
    positivity
  by_cases hDz : D=0
  · rw [hDz,min_eq_right hA]
    positivity
  pm_485 hAp A lt_of_le_of_ne hA Ne.symm hAz
  pm_485 hDp D lt_of_le_of_ne hD Ne.symm hDz
  by_cases hAD : A ≤ D
  · rw [min_eq_left hAD]
    calc
      A = A^(1-θ)*A^θ := by rw [← Real.rpow_add hAp]; norm_num
      _ ≤ _ := by gcongr
  · rw [min_eq_right (le_of_not_ge hAD)]
    calc
      D = D^(1-θ)*D^θ := by rw [← Real.rpow_add hDp]; norm_num
      _ ≤ _ := by gcongr; linarith

/-- Pointwise weak-power interpolation cancels the varying amplitude.
The later dyadic sum incurs only a logarithmic number of levels. -/
theorem weak_power_square_mass_bound {A D U p θ mass : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hU : 0 < U)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hpθ : p*θ=2)
    (hMassA : mass ≤ A) (hMassD : mass ≤ D*U^(-p)) :
    U^2*mass ≤ A^(1-θ)*D^θ := by
  have hMin := min_le_geometric_power hA
    (mul_nonneg hD (Real.rpow_nonneg hU.le (-p))) hθ hθ1
  have hh := mul_le_mul_of_nonneg_left ((le_min hMassA hMassD).trans hMin) (sq_nonneg U)
  have hExp : (-p)*θ = -2 := by grind
  rw [Real.mul_rpow hD (Real.rpow_nonneg hU.le (-p)),← Real.rpow_mul hU.le,hExp] at hh
  have hId : U^2*(A^(1-θ)*(D^θ*U^(-2:ℝ))) = A^(1-θ)*D^θ := by
    rw [Real.rpow_neg hU.le,Real.rpow_two]
    field_simp
  grind

end Montgomery.RationalMoment
