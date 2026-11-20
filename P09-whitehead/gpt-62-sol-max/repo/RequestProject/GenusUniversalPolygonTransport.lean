module

public import RequestProject.GenusUniversalPolygonReference
public import RequestProject.GenusAttachingRelativeOldBoundary

@[expose] public section

/-! Transport of the explicit pre-substitution degree-one polygon to the
actual named quotient. All chains retain their actual cover sheets.
 -/
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem cellularOrderHom_vertex_monotone (f : Hom (orderCx P) (orderCx Q)) :
    Monotone (show P → Q from f.onV) := by
  intro a b hab
  let e : OrdEdge P := ⟨(a, b), hab⟩
  have h := (f.onE e).2
  have hs : (f.onE e).1.1 = f.onV a := f.src_onE e
  have ht : (f.onE e).1.2 = f.onV b := f.tgt_onE e
  simp_all

variable {a : P}

theorem universalNerveChain2_uOrderHom (c : OrdTri (UOrder P a) →₀ ℤ) :
    universalNerveChain2 (chain2 uOrderHom c) = ordNerveChain2 c := by
  change ordNerveChain2 (chain2 uOrderHomInv (chain2 uOrderHom c)) = _
  rw [← chain2_comp_apply, uOrderHomInv_comp]
  simp [Hom.id]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve Cell
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- The source old-cover base is the actual spanning-tree root. The same
cylinder path used by the received comparison transports it to the quotient base. -/
def universalOldToNamedQuotient :
    Hom (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (namedQuotientCover ρ q u) :=
  (shiftHom (spineQuotientCylinderPath_isPath q ρ u)).comp
    (univLift (orderCx (QOld (cmpRel (GenusVertex q))))
      (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q))

def universalOldToNamedOrder (p : universalOldOrder q) :
    UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) :=
  (universalOldToNamedQuotient ρ q u).onV p

theorem universalOldToNamedOrder_monotone : Monotone (universalOldToNamedOrder ρ q u) := by
  have hm := cellularOrderHom_vertex_monotone
    (uOrderHomInv.comp ((universalOldToNamedQuotient ρ q u).comp uOrderHom))
  intro p r hpr
  have h := hm hpr
  change @LE.le (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) inferInstance
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u p))
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u r)) at h
  simpa only [uOrderHomInv_vertex] using h

theorem universalOldToNamedOrder_end (p : universalOldOrder q) :
    uOrderEnd (universalOldToNamedOrder ρ q u p) =
      qOldIncl (att := namedAtt ρ q u) (uOrderEnd p) := by
  change endV (shiftV (spineQuotientCylinderPath_isPath q ρ u)
    (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u) p)) = _
  aesop

theorem universalOldToNamedQuotient_nerve_chain2
    (c : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ) :
    universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u) c) =
      cmap (universalOldToNamedOrder ρ q u) (universalNerveChain2 c) := by
  let F := orderCxMap (universalOldToNamedOrder ρ q u) (universalOldToNamedOrder_monotone ρ q u)
  have he : uOrderHomInv.comp (universalOldToNamedQuotient ρ q u) = F.comp uOrderHomInv := by
    apply Hom.ext_orderCx
    funext x
    change uOrderHomInv.onV (universalOldToNamedOrder ρ q u x) =
      universalOldToNamedOrder ρ q u (uOrderHomInv.onV x)
    simp only [uOrderHomInv_vertex]
  change ordNerveChain2 (chain2 uOrderHomInv (chain2 _ c)) = _
  rw [← chain2_comp_apply, he, chain2_comp_apply, ordNerveChain2_chain2]
  rfl

theorem universalOldToNamedOrder_nerve_old (c : Ch (universalOldOrder q))
    (hc : c ∈ Inc _) :
    cmap (universalOldToNamedOrder ρ q u) c ∈
      IncOn (fun p => InQOld (uOrderEnd p)) := by
  apply cmap_mem_incOn_of_maps (universalOldToNamedOrder_monotone ρ q u) _ hc
  intro p
  rw [universalOldToNamedOrder_end]
  trivial

/-- The entire barycentric source cover maps into the genuine attaching
intersection, before applying the last-vertex projection. -/
def universalPolygonAttachingRealization
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) : namedAttachingCover q ρ u :=
  ⟨universalOldToNamedOrder ρ q u (universalPolygonRealization q σ), by
    rw [universalOldToNamedOrder_end, universalPolygonRealization_end]
    tauto⟩

theorem universalPolygonAttachingRealization_monotone :
    Monotone (universalPolygonAttachingRealization ρ q u) :=
  (universalOldToNamedOrder_monotone ρ q u).comp (universalPolygonRealization_monotone q)

theorem universalPolygonAttachingRealization_projection
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ) =
      barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ := by
  have h := qAttachingCoverEnd_spec (namedQuotientBase ρ q u)
    (universalPolygonAttachingRealization ρ q u σ)
  change qOldIncl (att := namedAtt ρ q u)
    (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ))) =
    uOrderEnd (universalOldToNamedOrder ρ q u (universalPolygonRealization q σ)) at h
  rw [universalOldToNamedOrder_end, universalPolygonRealization_end] at h
  exact Subtype.ext (congrArg (·.1.spx)
    (Sum.inl.inj h))

def universalPolygonToNamedSurface (p : UniversalPolygonCover q) : NamedSurfaceCover ρ q u :=
  namedSurfaceForward q ρ u
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
  let T := namedSurfaceForward q ρ u
  have hT := namedSurfaceForward_monotone q ρ u
  let s := universalPolygonAttachingRealization ρ q u (spx2 hpr)
  have hp  :=
    hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_left hpr))
  have hr : universalPolygonToNamedSurface ρ q u r ≤ T s :=
    hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_right hpr))
  have he : universalPolygonToNamedSurface ρ q u r = T s := by
    apply (namedSurfaceProjection_isPosetCover ρ q u).down_inj hr le_rfl
    rw [universalPolygonToNamedSurface_projection]
    change universalPolygonProjection q r =
      chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
        (universalPolygonAttachingRealization ρ q u (spx2 hpr)))
    rw [universalPolygonAttachingRealization_projection,
      barycentricMap_spx2]
    letI : DecidableEq (GenusVertex q) := Classical.decEq _
    exact (chainMax_spx2 ((universalPolygonProjection_isPosetCover q).mono hpr)).symm
  exact he.symm ▸ hp

theorem universalPolygonToNamedSurface_strictMono :
    StrictMono (universalPolygonToNamedSurface ρ q u) := by
  intro p r hpr
  apply lt_of_le_of_ne (universalPolygonToNamedSurface_monotone ρ q u hpr.le)
  intro he
  have hp := congrArg (namedSurfaceProjection ρ q u) he
  rw [universalPolygonToNamedSurface_projection, universalPolygonToNamedSurface_projection] at hp
  exact hpr.ne ((universalPolygonProjection_isPosetCover q).up_inj le_rfl hpr.le hp)

/-- Singleton lifts and general simplex lifts give the same surface sheet
at the maximal original cell. This is stronger than equality after projection. -/
theorem universalPolygonAttachingRealization_lastVertex
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    namedSurfaceForward q ρ u (universalPolygonAttachingRealization ρ q u σ) =
      universalPolygonToNamedSurface ρ q u (chainMax σ) := by
  have hs : spx1 (chainMax σ) ≤ σ := by
    intro p hp
    have he : p = chainMax σ := by simp_all
    rw [he]
    exact chainMax_mem σ
  have hm := namedSurfaceForward_monotone q ρ u
      (universalPolygonAttachingRealization_monotone ρ q u hs)
  apply Eq.symm
  apply (namedSurfaceProjection_isPosetCover ρ q u).down_inj hm le_rfl
  change namedSurfaceProjection ρ q u
    (universalPolygonToNamedSurface ρ q u (chainMax σ)) = _
  rw [universalPolygonToNamedSurface_projection]
  change universalPolygonProjection q (chainMax σ) =
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ))
  rw [universalPolygonAttachingRealization_projection]
  erw [chainMax_barycentricMap]

def transportedUniversalPolygonPole : NamedPolygonPole ρ q u :=
  ⟨universalPolygonToNamedSurface ρ q u (universalPolygonPole q).1,
    (universalPolygonToNamedSurface_projection ρ q u _).trans (universalPolygonPole q).2⟩

theorem universalPolygonToNamedSurface_fundamental :
    chain2 (strictOrderCxMap (universalPolygonToNamedSurface ρ q u)
      (universalPolygonToNamedSurface_strictMono ρ q u)) (universalPolygon q).cellularFundamental =
      namedPolygonFillingAt ρ q u (transportedUniversalPolygonPole ρ q u) := by
  have hsource : (universalPolygon q).cellularFundamental =
      polygonCoverFilling (gc q) (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q) (universalPolygonPole q) :=
    CoveredPolygon.cellularFundamental_unique (gc q) (universalPolygonProjection q)
      (universalPolygonProjection_isPosetCover q) (universalPolygon q) _
  rw [hsource]
  exact polygonCoverFilling_map (gc q) (universalPolygonProjection q)
    (universalPolygonProjection_isPosetCover q) (namedSurfaceProjection ρ q u)
    (namedSurfaceProjection_isPosetCover ρ q u) (universalPolygonToNamedSurface ρ q u)
    (universalPolygonToNamedSurface_strictMono ρ q u)
    (universalPolygonToNamedSurface_projection ρ q u) (universalPolygonPole q)

def transportedUniversalPolygonAttachingChain : Ch (namedAttachingCover q ρ u) :=
  ordNerveChain2 (chain2 (orderCxMap (universalPolygonAttachingRealization ρ q u)
    (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (universalPolygon q).fundamental))

theorem transportedUniversalPolygonAttachingChain_mem_inc :
    transportedUniversalPolygonAttachingChain ρ q u ∈ Inc _ := ordNerveChain2_mem_inc _

theorem transportedUniversalPolygonAttachingChain_degree :
    lengthProjection 3 (transportedUniversalPolygonAttachingChain ρ q u) =
      transportedUniversalPolygonAttachingChain ρ q u := ordNerveChain2_lengthProjection _

/-- Exact normalization to the actual lifted degree-one filling, at its
transported pole. No arbitrary nullhomotopy enters this identity. -/
theorem transportedUniversalPolygonAttachingChain_normalized :
    namedAttachingNerveSurfaceChain ρ q u (transportedUniversalPolygonAttachingChain ρ q u) =
      namedPolygonFillingAt ρ q u (transportedUniversalPolygonPole ρ q u) := by
  have hs : (namedSurfaceForwardHom q ρ u).comp
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) =
      (orderCxMap (universalPolygonToNamedSurface ρ q u)
        (universalPolygonToNamedSurface_monotone ρ q u)).comp
          (orderCxMap (chainMax (P := UniversalPolygonCover q)) chainMax_monotone) := by
    exact Hom.ext_orderCx (funext (universalPolygonAttachingRealization_lastVertex ρ q u))
  change normalizeOrdChain2 (chain2 (namedSurfaceForwardHom q ρ u)
    (decodeOrdNerve2 (ordNerveChain2 (chain2
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (universalPolygon q).fundamental))))) = _
  rw [decodeOrdNerve2_encode]
  rw [← chain2_comp_apply, hs, chain2_comp_apply,
    normalizeOrdChain2_strict_map _ (universalPolygonToNamedSurface_strictMono ρ q u),
    barycentricChain2_lastVertex]
  exact universalPolygonToNamedSurface_fundamental ρ q u

theorem universalPolygonAttachingRealization_square :
    (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) =
      (universalOldToNamedQuotient ρ q u).comp (universalPolygonLift q) := by
  exact Hom.ext_uCover_orderCx rfl

/-- The reference in the attaching intersection is the exact image of the
source old-cover polygon, with every sheet and face coefficient unchanged. -/
theorem transportedUniversalPolygonAttachingChain_image :
    cmap (Subtype.val : namedAttachingCover q ρ u → _)
      (transportedUniversalPolygonAttachingChain ρ q u) =
      universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u)
        (universalOldPolygonChain q)) := by
  let b := barycentricChain2 (universalPolygon q).fundamental
  have he (c : OrdTri (namedAttachingCover q ρ u) →₀ ℤ) :
      universalNerveChain2 (chain2 (namedAttachingIntoUniversal q ρ u) c) =
        cmap Subtype.val (ordNerveChain2 c) := by
    rw [namedAttachingIntoUniversal, chain2_comp_apply,
      universalNerveChain2_uOrderHom, ordNerveChain2_chain2]
  change cmap Subtype.val (ordNerveChain2 (chain2
    (orderCxMap (universalPolygonAttachingRealization ρ q u)
      (universalPolygonAttachingRealization_monotone ρ q u)) b)) = _
  rw [← he, ← chain2_comp_apply, universalPolygonAttachingRealization_square,
    chain2_comp_apply]
  rfl

/-- Any source old-cover chain in the selected polygon class is transported
to the explicit degree-one attaching reference, with an actual old correction. -/
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
    universalOldToNamedOrder_nerve_old ρ q u y hy, ?_⟩
  rw [universalOldToNamedQuotient_nerve_chain2, hcy, map_add, cmap_bdry,
    ← universalOldToNamedQuotient_nerve_chain2, ← transportedUniversalPolygonAttachingChain_image]

end FiniteChains.Davis.Genus
