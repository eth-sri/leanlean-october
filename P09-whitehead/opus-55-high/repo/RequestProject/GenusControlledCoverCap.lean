import RequestProject.GenusLiftedMarkingCorrection
import RequestProject.OrderConeCoverFans
import RequestProject.SurfaceFullCubeConeChains
import RequestProject.Tac
noncomputable section


/-! Controlled cap fillings in the actual full cube universal cover. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def markingCornerLift :=
  extend (coneRadial _
    _ (positiveCorner_le_surface _) (gBase q), false)
    (UV.base _ (fullCubeMarkBase q))

theorem markingCornerLift_end : endV (markingCornerLift q) =
    positiveCorner (cmpRel (GenusVertex q)) :=
  endV_extend (by rfl)

theorem markingCornerLift_reference_base :
    coneCoverReference (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q) (gBase q) =
      UV.base _ (fullCubeMarkBase q) := by
  have h := extend_revGerm (X := orderCx (QCube (cmpRel _)))
    (c := UV.base _ _)
    (eb := (coneRadial _
      _ (positiveCorner_le_surface _) (gBase q), false)) (by rfl)
  exact h

def markingCoverConeFan (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  coneCoverFan _ (surfaceFullCube_monotone _)
    _ (positiveCorner_le_surface _) _
    (markingCornerLift_end q) (pathChain (gSig q (x.1.val, x.2)))

theorem markingCoverConeFan_boundary x :
    Comb.bdry2 (fullCubeMarkCover q) (markingCoverConeFan q x) =
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  simp [markingCoverConeFan, coneCoverFan_loop_lift_boundary _ _ _ _ _ _
    (isPath_gSig q _), markingCornerLift_reference_base]

def markingOldImage (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  chain2 (univLift _ (oldToFullCube q) _) (liftedMarkingCorrection q x)

def controlledCoverCap (x : Fin q × Bool) :=
  markingOldImage q x + markingCoverConeFan q x

/-- The old-cover correction and the controlled cone fan fill the exact lifted cap loop. -/
theorem controlledCoverCap_boundary x :
    Comb.bdry2 (fullCubeMarkCover q) (controlledCoverCap q x) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) := by
  rwd [controlledCoverCap, map_add, markingOldImage, liftedMarkingCorrection_boundary, markingCoverConeFan_boundary]
  abel

/-- Its projection splits into old-block faces and the explicit positive-corner cone fan. -/
theorem controlledCoverCap_hurewicz x :
    hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) =
      chain2 (oldToFullCube q) (hurewicz _ (posQCube (gBase q)) (liftedMarkingCorrection q x)) +
        surfaceCornerFan (cmpRel (GenusVertex q)) (pathChain (gSig q (x.1.val, x.2))) := by
  rwd [controlledCoverCap, map_add]
  apply congrArg₂ _
  · exact hurewicz_univLift_chain2 _ _
      _
  · rwd [markingCoverConeFan, coneCoverFan_hurewicz]
    rfl
