module

public import RequestProject.GenusSpineConnected
public import RequestProject.GenusNamedSpineComparison
public import RequestProject.ReceivedTreeFiberCoordinates
public import RequestProject.StrictOrderPullbackHom
public import RequestProject.UniversalOrderChainBridge
public import RequestProject.GenusOldCoverSpineFaithfulness
public import RequestProject.GenusOldCoverSpineGeneration

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

def universalSpineToOld :
    Hom (markedSpineCx q) (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

abbrev universalSpineOldBase :=
  (universalSpineToOld q).onV (markedSpineTree q).root

def universalSpineOldReceiver :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q) :=
  (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q)).comp
    (namedSpineGroupEquiv q).symm.toMonoidHom

theorem universalSpineOldReceiver_bijective :
    Function.Bijective (universalSpineOldReceiver q) := by
  have hbij : Function.Bijective (pi1Map (universalSpineToOld q) (markedSpineTree q).root) := by
    erw [markedSpineTree_root, show pi1Map (universalSpineToOld q) (markedSpineBase q) =
      (genusSpineToOldPi1Equiv q).toMonoidHom.comp (markedSpinePi1Equiv q).toMonoidHom
      from MonoidHom.ext fun z => Quotient.inductionOn z fun _ => congrArg Pi1.mk
        (Subtype.ext (by simp only [universalSpineToOld, mapPath, Hom.comp, List.map_map, Function.comp_def]; rfl))]
    exact (genusSpineToOldPi1Equiv q).bijective.comp (markedSpinePi1Equiv q).bijective
  exact hbij.comp
    ((spinePresentationPi1Equiv q).symm.bijective.comp (namedSpineGroupEquiv q).symm.bijective)

def universalSpineWordReceiver :
    PresGroup (spinePresentation q) →* PresGroup (namedSpinePresentation q) :=
  (namedSpineGroupEquiv q).toMonoidHom

theorem universalSpineOldReceiver_compatible :
    (universalSpineOldReceiver q).comp (universalSpineWordReceiver q) =
      (pi1Map (universalSpineToOld q) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) :=
  MonoidHom.ext fun z => by
    change (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q))
      ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
    erw [MulEquiv.symm_apply_apply]; rfl

abbrev universalNamedSpineCover :=
  ReceivedTree.cover (markedSpineTree q) (universalSpineWordReceiver q)

def universalNamedSpineComparison :
    Hom (universalNamedSpineCover q)
      (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)) :=
  ReceivedTree.comparison (markedSpineTree q) (universalSpineToOld q)
    (universalSpineWordReceiver q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_compatible q)

abbrev universalOldOrder :=
  UOrder (QOld (cmpRel (GenusVertex q))) (universalSpineOldBase q)

theorem universalOldEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) := by
  let : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  exact uOrderEnd_isPosetCover isConnected_orderCx_qOld

def universalReceivedOrderMap :
    Hom (universalNamedSpineCover q) (orderCx (universalOldOrder q)) :=
  uOrderHomInv.comp (universalNamedSpineComparison q)

def universalReceivedStrictSpine :
    Hom (universalNamedSpineCover q) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (ReceivedTree.projection (markedSpineTree q) (universalSpineWordReceiver q))

theorem universalReceived_spine_square :
    (orderCxMap uOrderEnd (universalOldEnd_isPosetCover q).mono).comp
      (universalReceivedOrderMap q) =
      (orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        ((strictOrderIncl (GenusSpineCell q)).comp (universalReceivedStrictSpine q)) :=
  Hom.ext'
    (funext fun a => by
      change uOrderEnd (uOrderHomInv.onV
        (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
          (universalSpineOldReceiver q) a.1 a.2)) = _
      erw [uOrderHomInv_vertex]; exact ReceivedTree.receiverVertex_end _ _ _ _ _)
    (funext fun e => uOrderHomInv_edge_projection
      (ReceivedTree.receiverEdge (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) e.1 e.2))
    (funext fun t => uOrderHomInv_face_projection
      (ReceivedTree.receiverFace (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) t.1 t.2))

abbrev universalSpinePullback :=
  PosetCoverPullback (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
    (a := universalSpineOldBase q)) (genusSpineCellToOld q)

def universalReceivedToPullback :
    Hom (universalNamedSpineCover q) (strictOrderCx (universalSpinePullback q)) :=
  strictOrderPullbackHom uOrderEnd (universalOldEnd_isPosetCover q)
    (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
    (universalReceivedOrderMap q) (universalReceivedStrictSpine q)
    (universalReceived_spine_square q)

def universalSpinePullbackOldOrderIso :
    universalSpinePullback q ≃o OldCoveredSpine q
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)) where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def universalReceivedToCoveredSpine :
    Hom (universalNamedSpineCover q)
      (strictOrderCx (OldCoveredSpine q
        (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)))) :=
  (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
    (universalSpinePullbackOldOrderIso q).strictMono).comp (universalReceivedToPullback q)

theorem universalReceivedToCoveredSpine_onF_surjective :
    Function.Surjective (universalReceivedToCoveredSpine q).onF := by
  have hp_surj : Function.Surjective (universalReceivedToPullback q).onF := fun t => by
    let original := strictPullbackOriginal
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
      (genusSpineCellToOld q)
    let projection := strictPullbackProjection
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
      (universalOldEnd_isPosetCover q) (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
    obtain ⟨s, hs⟩ := markedSpine_component_onF_surjective q (projection.onF t)
    have ht : (uOrderFace (original.onF t)).1.2 = (universalSpineToOld q).onF s :=
      (Subtype.ext (Prod.ext t.1.1.2 (Prod.ext t.1.2.1.2 t.1.2.2.2))).trans
        (congrArg (genusSpineToOld q).onF hs).symm
    obtain ⟨g, hg⟩ := ReceivedTree.receiverFace_fiber_surjective
      (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
      (universalSpineOldReceiver_bijective q).2 s (uOrderFace (original.onF t)) ht
    have hp : (universalReceivedOrderMap q).onF (g, s) = original.onF t :=
      uOrderFace_injective ((homInv_onF_apply uOrderHom Function.bijective_id
        ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
        ⟨uOrderFace_injective, uOrderFace_surjective⟩ _).trans hg)
    exact ⟨(g, s), Subtype.ext (Prod.ext
      (Subtype.ext (Prod.ext (congrArg (·.1.1) hp) (congrArg (·.1.1) hs)))
      (Prod.ext
        (Subtype.ext (Prod.ext (congrArg (·.1.2.1) hp) (congrArg (·.1.2.1) hs)))
        (Subtype.ext (Prod.ext (congrArg (·.1.2.2) hp) (congrArg (·.1.2.2) hs)))))⟩
  intro t
  obtain ⟨c, hc⟩ := hp_surj ((strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
    (universalSpinePullbackOldOrderIso q).symm.strictMono).onF t)
  refine ⟨c, ?_⟩
  change (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
    (universalSpinePullbackOldOrderIso q).strictMono).onF
      ((universalReceivedToPullback q).onF c) = t
  erw [hc]; exact Subtype.ext (by simp only [strictOrderCxMap, OrderIso.apply_symm_apply])

theorem universalReceivedToCoveredSpine_onE_injective :
    Function.Injective (universalReceivedToCoveredSpine q).onE := by
  let toStrict : Hom (strictOrderCx (OldCoveredSpine q
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))))
      (strictOrderCx (GenusSpineCell q)) :=
    (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
      (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        (strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
          (universalSpinePullbackOldOrderIso q).symm.strictMono)
  rintro ⟨g, e⟩ ⟨h, d⟩ he
  cases Subtype.ext (congrArg toStrict.onE he)
  have hv : (universalReceivedToCoveredSpine q).onV ((universalNamedSpineCover q).src (g, e)) =
      (universalReceivedToCoveredSpine q).onV ((universalNamedSpineCover q).src (h, e)) := by
    erw [← (universalReceivedToCoveredSpine q).src_onE,
      ← (universalReceivedToCoveredSpine q).src_onE, he]
  have hv' := congrArg (oldCoveredSpineToOld q uOrderEnd) hv
  have hvold (a : (universalNamedSpineCover q).V) :
      oldCoveredSpineToOld q uOrderEnd ((universalReceivedToCoveredSpine q).onV a) =
        (universalNamedSpineComparison q).onV a := uOrderHomInv_vertex _
  erw [hvold, hvold] at hv'
  exact Prod.ext (ReceivedTree.receiverVertex_fiber_injective
    (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_bijective q).1 ((markedSpineCx q).src e) hv') rfl

theorem universalReceivedCoveredChain_nerve_image
    (d : (universalNamedSpineCover q).F →₀ ℤ) :
    Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
      (ordNerveChain2 (ordStrictInclusion2
        (chain2 (universalReceivedToCoveredSpine q) d))) =
      universalNerveChain2 (chain2 (universalNamedSpineComparison q) d) := by
  have hcomp {K Y Z : Complex2} (f : Hom K Y) (g : Hom Y Z) (c : K.F →₀ ℤ) :
      chain2 (g.comp f) c = chain2 g (chain2 f c) := by
    change Finsupp.mapDomain (g.onF ∘ f.onF) c = Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
    erw [Finsupp.mapDomain_comp]
  have hfirst : (orderCxMap (oldCoveredSpineToOld q uOrderEnd)
        (oldCoveredSpineToOld_monotone q uOrderEnd)).comp
      ((strictOrderIncl _).comp (universalReceivedToCoveredSpine q)) =
      universalReceivedOrderMap q := Hom.ext' rfl rfl rfl
  change Nerve.cmap _ (ordNerveChain2 (chain2 (strictOrderIncl _)
    (chain2 (universalReceivedToCoveredSpine q) d))) =
    ordNerveChain2 (chain2 uOrderHomInv (chain2 (universalNamedSpineComparison q) d))
  erw [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q uOrderEnd)]
  have h := congrArg ordNerveChain2 (congrArg (fun k => chain2 k d) hfirst)
  dsimp only [universalReceivedOrderMap] at h
  rwa [hcomp, hcomp, hcomp] at h

theorem universalSpine_adjust_filling
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : Nerve.Ch (universalOldOrder q))
    (hz : z ∈ Nerve.Inc (universalOldOrder q))
    (hd : Nerve.lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry
      (Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (universalReceivedToCoveredSpine q) d))))) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        z = Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
          (ordNerveChain2 (ordStrictInclusion2
            (chain2 (universalReceivedToCoveredSpine q) d'))) + Nerve.bdry y := by
  obtain ⟨c, hcb, y, hy, hzy⟩ := genus_old_cover_spine_adjust_filling q
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) (universalOldEnd_isPosetCover q)
    (chain2 (universalReceivedToCoveredSpine q) d) z hz hd hb
  obtain ⟨d', hd'⟩ : ∃ d', chain2 (universalReceivedToCoveredSpine q) d' = c :=
    Finsupp.mapDomain_surjective (universalReceivedToCoveredSpine_onF_surjective q) c
  have hinj : Function.Injective (chain1 (universalReceivedToCoveredSpine q)) :=
    Finsupp.mapDomain_injective (universalReceivedToCoveredSpine_onE_injective q)
  exact ⟨d', hinj (by erw [← bdry2_chain2, ← bdry2_chain2, hd']; exact hcb),
    y, hy, by erw [hd']; exact hzy⟩

theorem universalSpine_adjust_to_chain
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ)
    (hz : Comb.bdry2 _ z = chain1 (universalNamedSpineComparison q)
      (Comb.bdry2 (universalNamedSpineCover q) d)) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        universalNerveChain2 z = universalNerveChain2
          (chain2 (universalNamedSpineComparison q) d') + Nerve.bdry y := by
  obtain ⟨d', hbd, y, hy, hzy⟩ := universalSpine_adjust_filling q d
    (universalNerveChain2 z) (universalNerveChain2_mem_inc z)
    (universalNerveChain2_lengthProjection z)
    (by erw [universalReceivedCoveredChain_nerve_image, universalNerveChain2_bdry,
      universalNerveChain2_bdry, bdry2_chain2, hz])
  refine ⟨d', hbd, y, hy, ?_⟩
  rwa [universalReceivedCoveredChain_nerve_image] at hzy
