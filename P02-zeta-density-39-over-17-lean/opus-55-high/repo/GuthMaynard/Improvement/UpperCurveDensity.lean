module
public import GuthMaynard.Improvement.UpperCurveTypeICount
public import GuthMaynard.Improvement.WeakShortDensity
public import GuthMaynard.Improvement.WeakUpperDensity

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Uniform actual slab density, using the proved weaker moment.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem upper_curve_slab_density
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      5/7 ≤ σ → σ ≤ 3/4 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) := by pf_36 upper_curve_typeI_zero_slab_count 9 4

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem upper_curve_density
    {σ ε : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((9/4)*(1-σ)+ε) := by pf_230 upper_curve_slab_density 9 4

end GuthMaynard.Improvement
