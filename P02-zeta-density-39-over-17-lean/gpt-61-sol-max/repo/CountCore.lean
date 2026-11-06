module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

@[expose] public section

namespace LewkoDensityPalomar

/-- Analytic multiplicity of an actual global zeta zero in the closed height window.
The critical strip is open; the density and height cutoffs are closed. -/
noncomputable def zeroWeight (σ T : ℝ) (ρ : ℂ) : ℝ≥0∞ := by
  classical
  exact if riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) else 0

/-- The full count of actual zeta zeros with analytic multiplicity and both signs
of the ordinate. This is a genuine nonnegative extended-real sum. -/
noncomputable def zeroCount (σ T : ℝ) : ℝ≥0∞ := ∑' ρ : ℂ, zeroWeight σ T ρ

/-- An exact enumeration gives exactly the same multiplicity count. -/
theorem zeroCount_eq_finset (σ T : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    zeroCount σ T = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by
  classical
  calc
    zeroCount σ T = ∑ ρ ∈ F, zeroWeight σ T ρ := by
      apply tsum_eq_sum
      intro ρ hρ
      simp only [zeroWeight, ite_eq_right (mt (hF ρ).mpr hρ)]
    _ = ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp only [zeroWeight, ite_eq_left ((hF ρ).mp hρ)]
    _ = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by simp

end LewkoDensityPalomar
