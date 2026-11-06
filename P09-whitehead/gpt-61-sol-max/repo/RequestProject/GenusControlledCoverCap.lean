import Mathlib.Tactic

import RequestProject.GenusLiftedMarkingCorrection
import RequestProject.OrderConeCoverFans
import RequestProject.SurfaceFullCubeConeChains

/-! Controlled cap fillings in the actual full cube universal cover. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def markingCornerLift  :=
  extend (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
    (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)
    (UV.base _ (fullCubeMarkBase q))

theorem markingCornerLift_end : endV (markingCornerLift q) =
    positiveCorner (cmpRel (GenusVertex q)) :=
  endV_extend (rfl)

theorem markingCornerLift_reference_base :
    coneCoverReference (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q) (gBase q) =
      UV.base _ (fullCubeMarkBase q) := by
  have h := extend_revGerm (X := orderCx (QCube (cmpRel (GenusVertex q))))
    (c := UV.base _ (fullCubeMarkBase q))
    (eb := (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)) (rfl)
  exact h

variable (x : Fin q × Bool)
noncomputable def markingCoverConeFan   :=
  coneCoverFan (surfaceFullCube (cmpRel (GenusVertex q))) (surfaceFullCube_monotone _)
    (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q)
    (markingCornerLift_end q) (pathChain (gSig q (x.1.val, x.2)))

theorem markingCoverConeFan_boundary  :
    Comb.bdry2 (fullCubeMarkCover q) (markingCoverConeFan q x) =
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  rw  [markingCoverConeFan, coneCoverFan_loop_lift_boundary _ _ _ _ _ _
    (isPath_gSig q (x.1.val, x.2)), markingCornerLift_reference_base]

noncomputable def markingOldImage  : (fullCubeMarkCover q).F →₀ ℤ :=
  chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) (liftedMarkingCorrection q x)

noncomputable def controlledCoverCap   :=
  markingOldImage q x + markingCoverConeFan q x

/-- The old-cover correction and the controlled cone fan fill the exact lifted cap loop. -/
theorem controlledCoverCap_boundary  :
    Comb.bdry2 (fullCubeMarkCover q) (controlledCoverCap q x) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) := by
  rw  [controlledCoverCap, map_add, markingOldImage, liftedMarkingCorrection_boundary, markingCoverConeFan_boundary]
  abel

/-- Its projection splits into old-block faces and the explicit positive-corner cone fan. -/
theorem controlledCoverCap_hurewicz  :
    hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) =
      chain2 (oldToFullCube q) (hurewicz _ (posQCube (gBase q)) (liftedMarkingCorrection q x)) +
        surfaceCornerFan (cmpRel (GenusVertex q)) (pathChain (gSig q (x.1.val, x.2))) := by
  rw  [controlledCoverCap, map_add]
  apply congrArg₂ (· + ·)
  · solve_by_elim [FiniteChains.Comb.hurewicz_univLift_chain2]
  · rw  [markingCoverConeFan, coneCoverFan_hurewicz]
    rfl

end FiniteChains.Davis.Genus
