module

public import RequestProject.GenusUniversalPolygonReference
public import RequestProject.GenusAttachingRelativeOldBoundary

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {a : P}

theorem universalNerveChain2_uOrderHom (c : OrdTri (UOrder P a) →₀ ℤ) :
    universalNerveChain2 (chain2 uOrderHom c) = ordNerveChain2 c := by
  change ordNerveChain2
    (Finsupp.mapDomain uOrderHomInv.onF (Finsupp.mapDomain uOrderHom.onF c)) = _
  rw [← Finsupp.mapDomain_comp, show (uOrderHomInv (P := P) (a := a)).onF ∘ uOrderHom.onF = id
    from funext (homInv_onF_comp uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩), Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve Cell
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def universalOldToNamedQuotient :
    Hom (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (univLift (orderCx (QOld (cmpRel (GenusVertex q))))
      (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q))

def universalOldToNamedOrder (p : universalOldOrder q) :
    UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) :=
  (universalOldToNamedQuotient ρ q u).onV p

theorem universalOldToNamedOrder_monotone : Monotone (universalOldToNamedOrder ρ q u) := by
  intro p r hpr
  let f := uOrderHomInv.comp ((universalOldToNamedQuotient ρ q u).comp uOrderHom)
  let e : OrdEdge (universalOldOrder q) := ⟨(p, r), hpr⟩
  have h := (f.onE e).2
  have hs : (f.onE e).1.1 = f.onV p := f.src_onE e
  have ht : (f.onE e).1.2 = f.onV r := f.tgt_onE e
  rw [hs, ht] at h
  change @LE.le (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) inferInstance
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u p))
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u r)) at h
  simpa only [uOrderHomInv_vertex] using h

theorem universalOldToNamedOrder_end (p : universalOldOrder q) :
    uOrderEnd (universalOldToNamedOrder ρ q u p) =
      qOldIncl (att := namedAtt ρ q u) (uOrderEnd p) := by
  change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
    (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u) p)) = _
  rw [endV_pathTransportV, endV_univLiftV]; rfl

theorem universalOldToNamedOrder_edge (e : OrdEdge (universalOldOrder q)) :
    uOrderEdge ((orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)).onE e) =
      (universalOldToNamedQuotient ρ q u).onE (uOrderEdge e) :=
  Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext (universalOldToNamedOrder_end ρ q u e.1.1)
      (universalOldToNamedOrder_end ρ q u e.1.2))))

theorem universalOldToNamedOrder_face (t : OrdTri (universalOldOrder q)) :
    uOrderFace ((orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)).onF t) =
      (universalOldToNamedQuotient ρ q u).onF (uOrderFace t) :=
  Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext (universalOldToNamedOrder_end ρ q u t.1.1)
      (Prod.ext (universalOldToNamedOrder_end ρ q u t.1.2.1)
        (universalOldToNamedOrder_end ρ q u t.1.2.2)))))

theorem universalOldToNamedQuotient_nerve_chain2
    (c : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ) :
    universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u) c) =
      cmap (universalOldToNamedOrder ρ q u) (universalNerveChain2 c) := by
  have hsource : chain2 uOrderHom (chain2 uOrderHomInv c) = c := by
    change Finsupp.mapDomain uOrderHom.onF (Finsupp.mapDomain uOrderHomInv.onF c) = c
    rw [← Finsupp.mapDomain_comp, show uOrderHom.onF ∘ (uOrderHomInv
        (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)).onF = id
      from funext (homInv_onF_apply uOrderHom Function.bijective_id
        ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
        ⟨uOrderFace_injective, uOrderFace_surjective⟩), Finsupp.mapDomain_id]
  have hsq : uOrderHom.comp (orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)) =
      (universalOldToNamedQuotient ρ q u).comp uOrderHom :=
    Hom.ext' rfl (funext (universalOldToNamedOrder_edge ρ q u))
      (funext (universalOldToNamedOrder_face ρ q u))
  calc
    _ = universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 uOrderHom (chain2 uOrderHomInv c))) := by rw [hsource]
    _ = universalNerveChain2 (chain2 uOrderHom
        (chain2 (orderCxMap (universalOldToNamedOrder ρ q u)
          (universalOldToNamedOrder_monotone ρ q u)) (chain2 uOrderHomInv c))) := by
      rw [← chain2_comp_apply, ← hsq, chain2_comp_apply]
    _ = _ := by rw [universalNerveChain2_uOrderHom, ordNerveChain2_chain2]; rfl

def universalPolygonAttachingRealization
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) : namedAttachingCover q ρ u :=
  ⟨universalOldToNamedOrder ρ q u (universalPolygonRealization q σ), by
    rw [universalOldToNamedOrder_end, universalPolygonRealization_end]
    exact ⟨trivial, rfl⟩⟩

theorem universalPolygonAttachingRealization_monotone :
    Monotone (universalPolygonAttachingRealization ρ q u) :=
  (universalOldToNamedOrder_monotone ρ q u).comp (universalPolygonRealization_monotone q)

theorem universalPolygonAttachingRealization_projection
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ) =
      barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ := by
  have h : qOldIncl (att := namedAtt ρ q u)
      (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
        (universalPolygonAttachingRealization ρ q u σ))) =
      uOrderEnd (universalOldToNamedOrder ρ q u (universalPolygonRealization q σ)) :=
    qAttachingCoverEnd_spec (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ)
  rw [universalOldToNamedOrder_end, universalPolygonRealization_end] at h
  exact Subtype.ext (congrArg (fun t : QOld (cmpRel (GenusVertex q)) => t.1.spx) (Sum.inl.inj h))

def universalPolygonToNamedSurface (p : UniversalPolygonCover q) : NamedSurfaceCover ρ q u :=
  attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
      (universalPolygonAttachingRealization ρ q u (spx1 p))

theorem universalPolygonToNamedSurface_projection (p : UniversalPolygonCover q) :
    namedSurfaceProjection ρ q u (universalPolygonToNamedSurface ρ q u p) =
      universalPolygonProjection q p := by
  change chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
    (universalPolygonAttachingRealization ρ q u (spx1 p))) = _
  rw [universalPolygonAttachingRealization_projection, barycentricMap_spx1, chainMax_spx1]

theorem universalPolygonToNamedSurface_monotone :
    Monotone (universalPolygonToNamedSurface ρ q u) := by
  intro p r hpr
  let T := attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
  have hT := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  let s := universalPolygonAttachingRealization ρ q u (spx2 hpr)
  have he : universalPolygonToNamedSurface ρ q u r = T s := by
    refine (namedSurfaceProjection_isPosetCover ρ q u).down_inj
      (hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_right hpr))) le_rfl ?_
    rw [universalPolygonToNamedSurface_projection]
    change universalPolygonProjection q r =
      chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u) s)
    rw [universalPolygonAttachingRealization_projection, barycentricMap_spx2]
    let : DecidableEq (GenusVertex q) := Classical.decEq _
    exact (chainMax_spx2 ((universalPolygonProjection_isPosetCover q).mono hpr)).symm
  exact he.symm ▸ hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_left hpr))

theorem universalPolygonToNamedSurface_strictMono :
    StrictMono (universalPolygonToNamedSurface ρ q u) := fun _ _ hpr =>
  lt_of_le_of_ne (universalPolygonToNamedSurface_monotone ρ q u hpr.le) fun he => by
    have hp := congrArg (namedSurfaceProjection ρ q u) he
    rw [universalPolygonToNamedSurface_projection, universalPolygonToNamedSurface_projection] at hp
    exact hpr.ne ((universalPolygonProjection_isPosetCover q).up_inj le_rfl hpr.le hp)

theorem universalPolygonAttachingRealization_lastVertex
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (universalPolygonAttachingRealization ρ q u σ) =
      universalPolygonToNamedSurface ρ q u (chainMax σ) := by
  have hs : spx1 (chainMax σ) ≤ σ := fun p hp => by
    rw [show p = chainMax σ by simpa only [spx1, Finset.mem_singleton] using hp]
    exact chainMax_mem σ
  refine ((namedSurfaceProjection_isPosetCover ρ q u).down_inj
    (attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (universalPolygonAttachingRealization_monotone ρ q u hs))
    le_rfl ?_).symm
  change namedSurfaceProjection ρ q u (universalPolygonToNamedSurface ρ q u (chainMax σ)) = _
  rw [universalPolygonToNamedSurface_projection]
  change universalPolygonProjection q (chainMax σ) =
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ))
  rw [universalPolygonAttachingRealization_projection]
  erw [chainMax_barycentricMap]

def transportedUniversalPolygonPole : NamedPolygonPole ρ q u :=
  ⟨universalPolygonToNamedSurface ρ q u (universalPolygonPole q).1,
    (universalPolygonToNamedSurface_projection ρ q u _).trans (universalPolygonPole q).2⟩

def transportedUniversalPolygonAttachingChain : Ch (namedAttachingCover q ρ u) :=
  ordNerveChain2 (chain2 (orderCxMap (universalPolygonAttachingRealization ρ q u)
    (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)))

theorem transportedUniversalPolygonAttachingChain_mem_inc :
    transportedUniversalPolygonAttachingChain ρ q u ∈ Inc _ := ordNerveChain2_mem_inc _

theorem transportedUniversalPolygonAttachingChain_degree :
    lengthProjection 3 (transportedUniversalPolygonAttachingChain ρ q u) =
      transportedUniversalPolygonAttachingChain ρ q u := ordNerveChain2_lengthProjection _

theorem transportedUniversalPolygonAttachingChain_normalized :
    namedAttachingNerveSurfaceChain ρ q u (transportedUniversalPolygonAttachingChain ρ q u) =
      namedPolygonFillingAt ρ q u (transportedUniversalPolygonPole ρ q u) := by
  let F : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u)
  have hF : Monotone F := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  have hs : (orderCxMap F hF).comp
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) =
      (orderCxMap (universalPolygonToNamedSurface ρ q u)
        (universalPolygonToNamedSurface_monotone ρ q u)).comp
          (orderCxMap (chainMax (P := UniversalPolygonCover q)) chainMax_monotone) :=
    Hom.ext' (funext (universalPolygonAttachingRealization_lastVertex ρ q u))
      (funext fun _ => Subtype.ext (Prod.ext
        (universalPolygonAttachingRealization_lastVertex ρ q u _)
        (universalPolygonAttachingRealization_lastVertex ρ q u _)))
      (funext fun _ => Subtype.ext (Prod.ext
        (universalPolygonAttachingRealization_lastVertex ρ q u _)
        (Prod.ext (universalPolygonAttachingRealization_lastVertex ρ q u _)
          (universalPolygonAttachingRealization_lastVertex ρ q u _))))
  change normalizeOrdChain2 (chain2 (orderCxMap F hF)
    (decodeOrdNerve2 (ordNerveChain2 (chain2
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)))))) = _
  rw [decodeOrdNerve2_encode, ← chain2_comp_apply, hs, chain2_comp_apply,
    normalizeOrdChain2_strict_map _ (universalPolygonToNamedSurface_strictMono ρ q u),
    barycentricChain2_lastVertex]
  change chain2 (strictOrderCxMap (universalPolygonToNamedSurface ρ q u)
    (universalPolygonToNamedSurface_strictMono ρ q u)) (universalPolygon q).cellularFundamental = _
  rw [CoveredPolygon.cellularFundamental_unique (gc q) (universalPolygonProjection q)
      (universalPolygonProjection_isPosetCover q) (universalPolygon q)]
  exact polygonCoverFilling_map (gc q) (universalPolygonProjection q)
    (universalPolygonProjection_isPosetCover q) (namedSurfaceProjection ρ q u)
    (namedSurfaceProjection_isPosetCover ρ q u) (universalPolygonToNamedSurface ρ q u)
    (universalPolygonToNamedSurface_strictMono ρ q u)
    (universalPolygonToNamedSurface_projection ρ q u) (universalPolygonPole q)

theorem universalOldToNamedQuotient_polygon_reference
    (c : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ)
    (hgeometry : ∃ y ∈ Inc (universalOldOrder q),
      universalNerveChain2 c = universalNerveChain2 (universalOldPolygonChain q) + Nerve.bdry y) :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u) c) =
        cmap Subtype.val (transportedUniversalPolygonAttachingChain ρ q u) + Nerve.bdry y := by
  obtain ⟨y, hy, hcy⟩ := hgeometry
  refine ⟨cmap (universalOldToNamedOrder ρ q u) y,
    cmap_mem_incOn_of_maps (universalOldToNamedOrder_monotone ρ q u)
      (fun p => by rw [universalOldToNamedOrder_end]; trivial) hy, ?_⟩
  have himg : cmap (Subtype.val : namedAttachingCover q ρ u → _)
      (transportedUniversalPolygonAttachingChain ρ q u) =
      universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u)
        (universalOldPolygonChain q)) := by
    let b := barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)
    have he (d : OrdTri (namedAttachingCover q ρ u) →₀ ℤ) :
        universalNerveChain2 (chain2 (namedAttachingIntoUniversal q ρ u) d) =
          cmap Subtype.val (ordNerveChain2 d) := by
      rw [namedAttachingIntoUniversal, chain2_comp_apply,
        universalNerveChain2_uOrderHom, ordNerveChain2_chain2]
    have hsq : (namedAttachingIntoUniversal q ρ u).comp
        (orderCxMap (universalPolygonAttachingRealization ρ q u)
          (universalPolygonAttachingRealization_monotone ρ q u)) =
        (universalOldToNamedQuotient ρ q u).comp (universalPolygonLift q) :=
      Hom.ext' rfl
        (funext fun e => universalOldToNamedOrder_edge ρ q u
          ((orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q)).onE e))
        (funext fun t => universalOldToNamedOrder_face ρ q u
          ((orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q)).onF t))
    change cmap Subtype.val (ordNerveChain2 (chain2
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) b)) = _
    rw [← he, ← chain2_comp_apply, hsq, chain2_comp_apply]; rfl
  rw [universalOldToNamedQuotient_nerve_chain2, hcy, map_add, cmap_bdry,
    ← universalOldToNamedQuotient_nerve_chain2, ← himg]
