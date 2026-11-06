module

public import RequestProject.SurfaceFullCubeConeChains
public import RequestProject.GenusFullCubeMarking

@[expose] public section

/-! Concrete cap fillings split into an old-block marking correction and a positive cone fan. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Restoring the corner does not turn an old face's first vertex into that corner. -/
theorem oldToFullCube_face_ne_corner
    (f : (orderCx (QOld (cmpRel (GenusVertex q)))).F) :
    ((oldToFullCube q).onF f).1.1 ≠ positiveCorner (cmpRel (GenusVertex q)) := by
  intro h
  apply f.1.1.2
  exact ⟨congrArg QCube.spx h, congrArg QCube.sgn h⟩

end FiniteChains.Davis.Genus
