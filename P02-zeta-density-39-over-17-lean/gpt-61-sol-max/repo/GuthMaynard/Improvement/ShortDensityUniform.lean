module
public import GuthMaynard.Improvement.CurveUniformization
public import MathCollab.Density.ZetaCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

open Finset MathCollab.Density
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Uniformization for the actual multiplicity-weighted zero count. The
fixed-sigma hypothesis is explicit; no density estimate is postulated.
A finite grid spends half of epsilon, while the other half is supplied to
the fixed-sigma estimate. The resulting constant precedes sigma and height. -/
theorem zetaDensityCount_uniform_of_fixed_sigma {c : ℝ} (hc : 0 < c)
    (hfixed : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
        (zetaDensityCount σ T:ℝ) ≤ C*T^(c*(1-σ)+ε))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(c*(1-σ)+ε) := by
  apply density_curve_uniform_on_interval (by norm_num) hc ?_ hfixed hε
  intro x y hx hxy hy
  nlinarith

end GuthMaynard.Improvement
