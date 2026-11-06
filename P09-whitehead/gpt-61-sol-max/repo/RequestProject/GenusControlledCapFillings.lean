import Mathlib.Tactic

import RequestProject.SurfaceFullCubeConeChains
import RequestProject.GenusFullCubeMarking

/-! Concrete cap fillings split into an old-block marking correction and a positive cone fan. -/


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
