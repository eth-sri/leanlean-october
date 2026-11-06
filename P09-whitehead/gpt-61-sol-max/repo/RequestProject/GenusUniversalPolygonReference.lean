import Mathlib.Tactic

import RequestProject.GenusUniversalCoveredSpine
import RequestProject.GenusQuotientReceiver
import RequestProject.BarycentricCocycleCover
import RequestProject.CoveredPolygonBarycentricBoundary

/-! An explicit degree-one polygon in actual pre-substitution old-cover
sheets. No arbitrary surface nullhomotopy is used to select its class.
Pending final Lean verification. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

local instance : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩

def universalSpineOldReceiverEquiv  :=
  MulEquiv.ofBijective (universalSpineOldReceiver q) (universalSpineOldReceiver_bijective q)

theorem universalSpineOldBase_eq : universalSpineOldBase q = posQCube (gBase q) := by
  change (genusSpineToOld q).onV ((markedSpineTree q).root).1 = _
  rw  [markedSpineTree_root]
  rfl

abbrev exists_universalOldCocycle  :=
  OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld (universalSpineOldBase q)
    (universalSpineOldReceiverEquiv q).symm.toMonoidHom

def universalOldCocycle := Classical.choose (exists_universalOldCocycle q)

theorem universalOldCocycle_monodromy :
    (universalOldCocycle q).monodromy (universalSpineOldBase q) =
      (universalSpineOldReceiverEquiv q).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p => exact Classical.choose_spec (exists_universalOldCocycle q) p

theorem universalOldCocycle_monodromy_bijective :
    Function.Bijective ((universalOldCocycle q).monodromy (universalSpineOldBase q)) := by
  rw  [universalOldCocycle_monodromy]
  exact (universalSpineOldReceiverEquiv q).symm.bijective

abbrev UniversalPolygonCover :=
  DescendedSurfaceCover (posQCube (A := cmpRel (GenusVertex q)))
    posQCube_monotone (universalOldCocycle q)

def universalPolygonProjection  :=
  descendedSurfaceProjection posQCube posQCube_monotone (universalOldCocycle q)

abbrev universalPolygonProjection_isPosetCover  :=
  FiniteChains.Davis.descendedSurfaceProjection_isPosetCover FiniteChains.Davis.posQCube
    FiniteChains.Davis.posQCube_monotone (FiniteChains.Davis.Genus.universalOldCocycle q)

def universalPolygonRawPole : PolygonCoverPole (gc q) (universalPolygonProjection q) :=
  ⟨⟨cC (gc q), 1⟩, rfl⟩

def universalPolygonRaw := coveredPolygon (gc q) (universalPolygonProjection q)
  (universalPolygonProjection_isPosetCover q) (universalPolygonRawPole q)

def universalPolygonShift  :=
  (descendedSurfaceCocycle posQCube posQCube_monotone (universalOldCocycle q)).coverDeck
    ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet⁻¹

def universalPolygonPole  :=
  CoveredPolygon.mapPole (gc q) (universalPolygonProjection q) (universalPolygonProjection q)
    (universalPolygonShift q) (fun _ => rfl) (v := universalPolygonRawPole q)

/-- All polygon positions are translated together so the first boundary
vertex is in the identity sheet. The actual polygon orientation is retained. -/
def universalPolygon  :=
  (universalPolygonRaw q).map (gc q) (universalPolygonProjection q)
    (universalPolygonProjection q) (universalPolygonShift q)
    (universalPolygonShift q).monotone (fun _ => rfl)

theorem universalPolygon_initial_sheet :
    ((universalPolygon q).V (cyc (8 * q) 0)).sheet = 1 := inv_mul_cancel _

def universalPolygonRealization  :=
  barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

abbrev universalPolygonRealization_monotone  :=
  FiniteChains.Davis.barycentricCoverRealization_monotone FiniteChains.Davis.posQCube FiniteChains.Davis.posQCube_monotone
    (FiniteChains.Davis.Genus.universalOldCocycle q) (FiniteChains.Davis.Genus.universalSpineOldBase q)
    FiniteChains.Davis.isConnected_orderCx_qOld (FiniteChains.Davis.Genus.universalOldCocycle_monodromy_bijective q)

def universalPolygonLift  :=
  uOrderHom.comp (orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q))

theorem universalPolygonRealization_end (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    uOrderEnd (universalPolygonRealization q σ) =
      posQCube (barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ) :=
  barycentricCoverRealization_end posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q) σ

theorem universalPolygonLift_projects :
    (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)).comp
      (universalPolygonLift q) =
      (surfCx (cmpRel (GenusVertex q))).comp
        (orderCxMap (barycentricMap (universalPolygonProjection q)
          (universalPolygonProjection_isPosetCover q).mono)
          (barycentricMap_monotone _ (universalPolygonProjection_isPosetCover q).mono)) := by apply Hom.ext' <;> funext x <;> solve_by_elim (maxDepth := 10) [Subtype.ext, Prod.ext, universalPolygonRealization_end]

theorem universalPolygonLift_initial :
    (universalPolygonLift q).onV (spx1 ((universalPolygon q).V (cyc (8 * q) 0))) =
      UV.base _ (universalSpineOldBase q) := by
  apply (universalOldCocycle q).readVertex_fibre_injective (universalSpineOldBase q)
    (universalOldCocycle_monodromy_bijective q).1
  · change uOrderEnd (universalPolygonRealization q _) = _
    rw  [universalPolygonRealization_end, barycentricMap_spx1,
      (universalPolygon q).projV, endV_base, universalSpineOldBase_eq]
    rfl
  · change (universalOldCocycle q).readVertex (universalSpineOldBase q)
      (barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
        (universalSpineOldBase q) isConnected_orderCx_qOld
        (universalOldCocycle_monodromy_bijective q) _) = _
    rw (config := { transparency := .default }) [barycentricCoverRealization_read]
    simp_all [barycentricCoverReading, descendedSurfaceSimplex, descendedSurfaceProjection, universalPolygon_initial_sheet]

/-- The subdivided source polygon, now in actual old universal-cover cells. -/
def universalOldPolygonChain  :=
  chain2 (universalPolygonLift q)
    (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental))

theorem universalOldPolygonChain_boundary :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      pathChain (uLiftPath (mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)))
        (UV.base _ (universalSpineOldBase q))) := by
  rw  [universalOldPolygonChain, bdry2_chain2,
    (universalPolygon q).subdivisionFundamental_boundary (gc q) (universalPolygonProjection q)]
  change Finsupp.mapDomain (universalPolygonLift q).onE (pathChain _) = _
  rw  [← pathChain_map]
  apply congrArg pathChain
  have hp := isPath_mapPath (universalPolygonLift q)
    ((universalPolygon q).subdivisionBoundaryPath_isPath (gc q) (universalPolygonProjection q) (8 * q))
  rw  [universalPolygonLift_initial] at hp
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (mapPath (universalPolygonLift q)
        ((universalPolygon q).subdivisionBoundaryPath (gc q) (universalPolygonProjection q) (8 * q))) =
      mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
    rw  [mapPath_comp, universalPolygonLift_projects, ← mapPath_comp,
      (universalPolygon q).subdivisionBoundaryPath_projection (gc q)
        (universalPolygonProjection q) (universalPolygonProjection_isPosetCover q)]
    congr 2 <;> exact Subsingleton.elim _ _
  rw  [hproj] at he
  exact he

end FiniteChains.Davis.Genus
