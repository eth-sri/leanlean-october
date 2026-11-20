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
noncomputable def surfaceCornerFan :=
  coneEdgeChain _ (surfaceFullCube_monotone A)
    _ (positiveCorner_le_surface A)

end FiniteChains.Davis
