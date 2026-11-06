module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalMomentPrimitive

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory
open scoped ComplexConjugate

/-- The weighted integral with the same denominator sign as winding number. -/
def physicalWeightedCauchy (γ K : ComplexCurve) z  :=
  ∫ θ in (0 : ℝ)..circlePeriod, (deriv γ θ * K θ) / (γ θ - z)

/-- The ordinary transform previously used for exterior analyticity has the
opposite denominator.  This exact identity records both that sign and the
conjugation of its physical density. -/
theorem physicalOrdinaryCauchy_eq_neg_weighted γ H w :
    physicalOrdinaryCauchy γ H w =
      -physicalWeightedCauchy γ (fun θ => conj (H θ)) w := by
  rw [physicalOrdinaryCauchy, physicalWeightedCauchy, ← intervalIntegral.integral_neg]
  grind

end PolyaNeumann

end
