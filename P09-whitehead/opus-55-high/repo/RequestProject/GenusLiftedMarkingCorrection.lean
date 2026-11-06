import RequestProject.LiftedHomotopyChains
import RequestProject.GenusEquivariantCapFillings
noncomputable section


/-! Genuine old-block cover chains correcting the surviving-spine marking to its surface loop. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

abbrev markingOldCover :=
  uCover (orderCx (QOld (cmpRel _))) (posQCube (gBase q))

/-- The marking correction is supported on actual old-block cover faces. -/
theorem exists_lifted_marking_correction x :
    ∃ d : (markingOldCover q).F →₀ ℤ,
      Comb.bdry2 (fullCubeMarkCover q)
        (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) d) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) -
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  have hp := (spineMarkedLoop_toOld_htpy q x).symm.isPath
    (isPath_mapPath _ (isPath_gSig q _))
  obtain ⟨d, hd⟩ := @exists_mapped_lifted_homotopy_chain
    _ _
    _ (oldToFullCube q)
    (UV.base (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)))
    _
    _
    _ hp (spineMarkedLoop_toOld_htpy q x)
  have he1 : mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1) =
      mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1 := by
    convert congrArg (fun p => mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) p)) (markedSpineLoop_inclusion q x).symm using 1 <;>
      simp only [markedSpineToFullCube, mapPath, Hom.comp, List.map_map, Function.comp_def] <;> rfl
  aesop

def liftedMarkingCorrection (x : Fin q × Bool) :=
  Classical.choose (exists_lifted_marking_correction q x)

theorem liftedMarkingCorrection_boundary x :
    Comb.bdry2 (fullCubeMarkCover q)
      (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q)))
        (liftedMarkingCorrection q x)) =
    pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
      (UV.base _ (fullCubeMarkBase q))) -
    pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
      (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
      (UV.base _ (fullCubeMarkBase q))) :=
  Classical.choose_spec (exists_lifted_marking_correction q x)
