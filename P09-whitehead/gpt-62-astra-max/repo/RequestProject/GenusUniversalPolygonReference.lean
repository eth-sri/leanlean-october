module

public import RequestProject.GenusUniversalCoveredSpine
public import RequestProject.GenusQuotientReceiver
public import RequestProject.BarycentricCocycleCover
public import RequestProject.CoveredPolygonBarycentricBoundary

@[expose] public section

/-! An explicit degree-one polygon in actual pre-substitution old-cover
sheets. No arbitrary surface nullhomotopy is used to select its class.
Pending final Lean verification. -/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

local instance : Nonempty (GenusVertex q) := ⟨cV _ (cyc (8 * q) 0)⟩

def universalSpineOldReceiverEquiv :=
  MulEquiv.ofBijective _ (universalSpineOldReceiver_bijective q)

theorem universalSpineOldBase_eq : universalSpineOldBase q = posQCube (gBase q) := by
  change (genusSpineToOld q).onV _ = _
  erw [markedSpineTree_root]
  rfl

theorem exists_universalOldCocycle :
    ∃ c : OrdCocycle (QOld _) (PresGroup _),
      ∀ p : Loop _ _,
        c.readPath p.1 = (universalSpineOldReceiverEquiv q).symm (Pi1.mk p) :=
  OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld _
    (universalSpineOldReceiverEquiv q).symm.toMonoidHom

def universalOldCocycle := Classical.choose (exists_universalOldCocycle q)

theorem universalOldCocycle_monodromy :
    (universalOldCocycle q).monodromy _ =
      (universalSpineOldReceiverEquiv q).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p => exact Classical.choose_spec (exists_universalOldCocycle q) p

theorem universalOldCocycle_monodromy_bijective :
    Function.Bijective ((universalOldCocycle q).monodromy (universalSpineOldBase q)) := by
  erw [universalOldCocycle_monodromy]
  exact (universalSpineOldReceiverEquiv q).symm.bijective

abbrev UniversalPolygonCover :=
  DescendedSurfaceCover _
    posQCube_monotone (universalOldCocycle q)

def universalPolygonProjection :=
  descendedSurfaceProjection posQCube posQCube_monotone (universalOldCocycle q)

theorem universalPolygonProjection_isPosetCover : IsPosetCover (universalPolygonProjection q) :=
  descendedSurfaceProjection_isPosetCover posQCube posQCube_monotone _

def universalPolygonRawPole : PolygonCoverPole _ (universalPolygonProjection q) :=
  ⟨⟨cC _, 1⟩, rfl⟩

def universalPolygonRaw := coveredPolygon _ _
  (universalPolygonProjection_isPosetCover q) (universalPolygonRawPole q)

def universalPolygonShift :=
  (descendedSurfaceCocycle posQCube posQCube_monotone (universalOldCocycle q)).coverDeck
    ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet⁻¹

def universalPolygonPole :=
  CoveredPolygon.mapPole _ _ (universalPolygonProjection q)
    (universalPolygonShift q) (fun _ => rfl) (v := universalPolygonRawPole q)

/-- All polygon positions are translated together so the first boundary
vertex is in the identity sheet. The actual polygon orientation is retained. -/
def universalPolygon : CoveredPolygon _ _
    (universalPolygonPole q) :=
  (universalPolygonRaw q).map _ _
    _ _
    (universalPolygonShift q).monotone _

theorem universalPolygon_initial_sheet :
    ((universalPolygon q).V (cyc (8 * q) 0)).sheet = 1 := by
  apply inv_mul_cancel

def universalPolygonRealization :=
  barycentricCoverRealization posQCube posQCube_monotone _
    _ isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

theorem universalPolygonRealization_monotone : Monotone (universalPolygonRealization q) :=
  barycentricCoverRealization_monotone posQCube posQCube_monotone _
    _ isConnected_orderCx_qOld
    _

def universalPolygonLift :=
  uOrderHom.comp (orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q))

theorem universalPolygonRealization_end (σ : NeSpx _) :
    uOrderEnd (universalPolygonRealization q σ) =
      posQCube (barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ) :=
  barycentricCoverRealization_end posQCube posQCube_monotone _
    _ isConnected_orderCx_qOld
    _ σ

theorem universalPolygonLift_projects :
    (univProj _ _).comp
      (universalPolygonLift q) =
      (surfCx (cmpRel _)).comp
        (orderCxMap (barycentricMap (universalPolygonProjection q)
          (universalPolygonProjection_isPosetCover q).mono)
          (barycentricMap_monotone _ (universalPolygonProjection_isPosetCover q).mono)) := by
  apply Hom.ext'
  · funext σ
    exact universalPolygonRealization_end q σ
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q e.1.1)
      (universalPolygonRealization_end q e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q t.1.1)
      (Prod.ext (universalPolygonRealization_end q t.1.2.1)
        (universalPolygonRealization_end q t.1.2.2))

theorem universalPolygonLift_initial :
    (universalPolygonLift q).onV (spx1 ((universalPolygon q).V (cyc (8 * q) 0))) =
      UV.base _ _ := by
  apply (universalOldCocycle q).readVertex_fibre_injective _
    (universalOldCocycle_monodromy_bijective q).1
  · change uOrderEnd (universalPolygonRealization q _) = _
    erw [universalPolygonRealization_end, barycentricMap_spx1,
      (universalPolygon q).projV, endV_base, universalSpineOldBase_eq] <;> rfl
  · change (universalOldCocycle q).readVertex _
      (barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
        (universalSpineOldBase q) isConnected_orderCx_qOld
        (universalOldCocycle_monodromy_bijective q) _) = _
    simp [barycentricCoverRealization_read, barycentricCoverReading, chainMax_spx1, descendedSurfaceSimplex, barycentricMap_spx1, descendedSurfaceProjection, OrdCocycle.val_refl, mul_one, universalPolygon_initial_sheet, OrdCocycle.readVertex_base]

/-- The subdivided source polygon, now in actual old universal-cover cells. -/
def universalOldPolygonChain :=
  chain2 (universalPolygonLift q)
    (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental))

theorem universalOldPolygonChain_boundary :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      pathChain (uLiftPath (mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)))
        (UV.base _ (universalSpineOldBase q))) := by
  erw [universalOldPolygonChain, bdry2_chain2,
    (universalPolygon q).subdivisionFundamental_boundary _ _]
  change Finsupp.mapDomain _ (pathChain _) = _
  erw [← pathChain_map]
  apply congrArg pathChain
  have hp := isPath_mapPath (universalPolygonLift q)
    ((universalPolygon q).subdivisionBoundaryPath_isPath (gc q) (universalPolygonProjection q) (8 * q))
  erw [universalPolygonLift_initial] at hp
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (mapPath (universalPolygonLift q)
        ((universalPolygon q).subdivisionBoundaryPath (gc q) (universalPolygonProjection q) (8 * q))) =
      mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
    erw [mapPath_comp, universalPolygonLift_projects, ← mapPath_comp,
      (universalPolygon q).subdivisionBoundaryPath_projection _
        _ (universalPolygonProjection_isPosetCover q)]
    congr 2 <;> exact Subsingleton.elim _ _
  erw [hproj] at he <;> assumption

end FiniteChains.Davis.Genus
