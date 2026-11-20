module

public import RequestProject.NormalizedStrictBoundary
public import RequestProject.PresCoverConeCylinderDecomposition

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))

/-- The actual cylinder collapse kills the boundary of every genuine finite triangle chain. -/
theorem cylinderCover_collapse_boundary_zero {f : P → CylBase w}
    (hf : IsPosetCover f) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf)
      (Comb.bdry2 (strictOrderCx P) c) = 0 := by
  erw [← bdry2_normalizedStrictChain2, cylinderCover_normalized_collapse_zero, map_zero]

variable (f : P → PresPos w) (hf : IsPosetCover f)

/-- The genuine collapse on the actual cylinder preimage in a presentation cover. -/
noncomputable def presCoverCylinderCollapse :
    {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →
      {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  cylinderCoverCollapse w (coneAdjCoverBaseEnd_isPosetCover f hf)

theorem presCoverCylinderCollapse_monotone : Monotone (presCoverCylinderCollapse w f hf) :=
  cylinderCoverCollapse_monotone w (coneAdjCoverBaseEnd_isPosetCover f hf)

end FiniteChains.PresModel
