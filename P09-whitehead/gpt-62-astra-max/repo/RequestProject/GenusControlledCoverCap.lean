module

public import RequestProject.GenusLiftedMarkingCorrection
public import RequestProject.OrderConeCoverFans
public import RequestProject.SurfaceFullCubeConeChains

@[expose] public section

/-! Controlled cap fillings in the actual full cube universal cover. -/

noncomputable section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def markingCornerLift :=
  extend (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
    (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)
    (UV.base _ (fullCubeMarkBase q))

theorem markingCornerLift_end : endV (markingCornerLift q) =
    positiveCorner _ :=
  endV_extend (rfl)

theorem markingCornerLift_reference_base :
    coneCoverReference _
      _ (positiveCorner_le_surface _) (markingCornerLift q) (gBase q) =
      UV.base _ _ := by
  have h := extend_revGerm
    (c := UV.base _ (fullCubeMarkBase q))
    (eb := (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)) (rfl)
  exact h

variable (x : Fin q × Bool)

def markingCoverConeFan :=
  coneCoverFan _ (surfaceFullCube_monotone _)
    _ (positiveCorner_le_surface _) (markingCornerLift q)
    (markingCornerLift_end q) (pathChain (gSig q (x.1.val, x.2)))

theorem markingCoverConeFan_boundary :
    Comb.bdry2 _ (markingCoverConeFan q x) =
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  erw [markingCoverConeFan, coneCoverFan_loop_lift_boundary _ _ _ _ _ _
    (isPath_gSig q _), markingCornerLift_reference_base]

def markingOldImage : (fullCubeMarkCover q).F →₀ ℤ :=
  chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) (liftedMarkingCorrection q x)

def controlledCoverCap :=
  markingOldImage q x + markingCoverConeFan q x

/-- The old-cover correction and the controlled cone fan fill the exact lifted cap loop. -/
theorem controlledCoverCap_boundary :
    Comb.bdry2 _ (controlledCoverCap q x) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) := by
  erw [controlledCoverCap, map_add, markingOldImage, liftedMarkingCorrection_boundary, markingCoverConeFan_boundary]
  abel

/-- Its projection splits into old-block faces and the explicit positive-corner cone fan. -/
theorem controlledCoverCap_hurewicz :
    hurewicz _ _ (controlledCoverCap q x) =
      chain2 (oldToFullCube q) (hurewicz _ (posQCube (gBase q)) (liftedMarkingCorrection q x)) +
        surfaceCornerFan _ (pathChain (gSig q (x.1.val, x.2))) := by
  erw [controlledCoverCap, map_add]
  apply congrArg₂ _
  · apply hurewicz_univLift_chain2
  · solve_by_elim [coneCoverFan_hurewicz]

end FiniteChains.Davis.Genus
