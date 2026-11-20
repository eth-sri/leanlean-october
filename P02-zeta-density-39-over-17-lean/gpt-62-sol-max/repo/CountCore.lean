module

public import MathCollab.Density.ZetaCounting
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

open MathCollab.Density

/-- The ENNReal sum and the finite sum count the same zeros with multiplicity. -/
theorem zeroCount_eq_density (σ T : ℝ) : zeroCount σ T = (zetaDensityCount σ T : ℝ≥0∞) := by
  classical
  have mem (ρ : ℂ) : ρ ∈ zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    simp only [mem_zetaDensityFinset, IsNontrivialZetaZero, and_assoc]
  rw [zeroCount, zetaDensityCount, zetaSlabCount, Nat.cast_sum, tsum_eq_sum]
  · exact Finset.sum_congr rfl fun ρ hρ => by simp [zeroWeight, zetaMultiplicity, (mem ρ).mp hρ]
  · intro ρ hρ
    simp [zeroWeight, mt (mem ρ).mpr hρ]

end LewkoDensityPalomar
