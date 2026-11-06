module

public import RequestProject.OrderConeChains
public import RequestProject.SurfaceFullCubeFilling

@[expose] public section

/-! Explicit cone-edge fans for the actual cut-surface inclusion. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The explicit positive-corner fan on a finite surface edge chain. -/
noncomputable def surfaceCornerFan :
    ((orderCx (NeSpx A)).E →₀ ℤ) →ₗ[ℤ] ((orderCx (QCube A)).F →₀ ℤ) :=
  coneEdgeChain (surfaceFullCube A) (surfaceFullCube_monotone A)
    (positiveCorner A) (positiveCorner_le_surface A)

end FiniteChains.Davis
