module

public import RequestProject.PhysicalMomentPrimitive

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory
open scoped ComplexConjugate

/-- The weighted integral with the same denominator sign as winding number. -/
def physicalWeightedCauchy (γ K : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv γ θ * K θ) / (γ θ - z)

/-- The ordinary transform previously used for exterior analyticity has the
opposite denominator.  This exact identity records both that sign and the
conjugation of its physical density. -/
theorem physicalOrdinaryCauchy_eq_neg_weighted (γ H : ℝ → ℂ) (w : ℂ) :
    physicalOrdinaryCauchy γ H w =
      -physicalWeightedCauchy γ (fun θ => conj (H θ)) w := by
  rw [physicalWeightedCauchy, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  grind

end PolyaNeumann

end
