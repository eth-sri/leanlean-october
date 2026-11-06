module

public import RequestProject.GenusUniversalPolygonTransport
public import RequestProject.GenusSingleSpineReference

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {K X Y : Complex2.{u}}

theorem univLiftV_extendList (f : Hom X Y) (a : X.V) :
    ∀ {p : List (X.E × Bool)} (v : UV X a) {b : X.V},
      IsPath X.src X.tgt p (endV v) b →
      univLiftV a f (extendList p v) = extendList (mapPath f p) (univLiftV a f v)
  | [], _, _, _ => rfl
  | e :: p, v, _, hp => by
      change univLiftV a f (extendList p (extend e v)) =
        extendList (mapPath f p) (extend (f.onE e.1, e.2) (univLiftV a f v))
      rw [univLiftV_extendList f a (extend e v) (by rw [endV_extend hp.1]; exact hp.2),
        univLiftV_extend a f hp.1]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem universalSpineOldReceiver_to_single_old
    (g : PresGroup (namedSpinePresentation q)) :
    finiteSpineOldRootReceiver q ρ u hrho (singleSpineNamedReceiver ρ q u g) =
      pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (universalSpineOldReceiver q g) := by
  obtain ⟨z, rfl⟩ := (namedSpineGroupEquiv q).surjective g
  exact (DFunLike.congr_fun (finiteSpineOldRootReceiver_compatible q ρ u hrho) z).trans
    ((pi1Map_comp_apply (universalSpineToOld q) (oldIntoNamedQuotient q ρ u)
      (markedSpineTree q).root _).trans
      (congrArg (pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q))
        (DFunLike.congr_fun (universalSpineOldReceiver_compatible q) z).symm))

theorem universalNamedSpineComparison_vertex_factor
    (g : PresGroup (namedSpinePresentation q)) (a : (markedSpineCx q).V) :
    (receivedSpineToQuotient q ρ u hrho).onV (singleSpineNamedReceiver ρ q u g, a) =
      (universalOldToNamedQuotient ρ q u).onV
        ((universalNamedSpineComparison q).onV (g, a)) := by
  have he : univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) g a) =
      ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (finiteSpineOldRootReceiver q ρ u hrho) (singleSpineNamedReceiver ρ q u g) a := by
    rw [ReceivedTree.receiverVertex, univLiftV_deckV,
      SpanningTree.mappedTreeReference,
      univLiftV_extendList (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (UV.base _ _) (isPath_mapPath (universalSpineToOld q) ((markedSpineTree q).treePath_isPath a)),
      ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
    change deckV _ (extendList (mapPath (oldIntoNamedQuotient q ρ u)
      (mapPath (universalSpineToOld q) ((markedSpineTree q).treePath a))) (UV.base _ _)) = _
    rw [mapPath_comp]; rfl
  exact congrArg (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)) he.symm

theorem universalOldToNamedQuotient_baseTransport_vertex
    (v : UV (spineOldCx q) (spineOldBase q)) :
    (universalOldToNamedQuotient ρ q u).onV ((universalOldBaseTransport q).onV v) =
      (oldCoverToNamedQuotient q ρ u).onV v := by
  induction v using UV.ind with | h p =>
  exact congrArg UV.mk (Subtype.ext rfl)

theorem singleFiniteSpineReference_corrected_geometry :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      quotientCorrectedRelativeNerveChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
        cmap Subtype.val (transportedUniversalPolygonAttachingChain ρ q u) + Nerve.bdry y := by
  have hsq1 : (receivedSpineToQuotient q ρ u hrho).comp
      (ReceivedTree.changeGroup (markedSpineTree q) (universalSpineWordReceiver q)
        (singleSpineNamedReceiver ρ q u)) =
      (universalOldToNamedQuotient ρ q u).comp (universalNamedSpineComparison q) :=
    Hom.ext' (funext fun x => universalNamedSpineComparison_vertex_factor ρ q u hrho x.1 x.2)
      (funext fun e => Subtype.ext (Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho e.1 _) rfl))
      (funext fun t => Subtype.ext (Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho t.1 _) rfl))
  have hsq2 : (universalOldToNamedQuotient ρ q u).comp (universalOldBaseTransport q) =
      oldCoverToNamedQuotient q ρ u :=
    Hom.ext' (funext (universalOldToNamedQuotient_baseTransport_vertex ρ q u))
      (funext fun e => Subtype.ext (Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u e.1.1) rfl))
      (funext fun t => Subtype.ext (Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u t.1.1) rfl))
  have hdeck (g : PresGroup (namedSpinePresentation q))
      (c : (uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ) :
      chain2 (universalOldToNamedQuotient ρ q u)
        ((univDeck (spineOldCx q) (universalSpineOldBase q)).faceChains
          (universalSpineOldReceiver q g) c) =
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains
          (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g))
          (chain2 (universalOldToNamedQuotient ρ q u) c) := by
    change Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF
        (Finsupp.mapDomain (deckF (universalSpineOldReceiver q g)) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    refine congrArg (Finsupp.mapDomain · c) (funext fun t => Subtype.ext (Prod.ext ?_ rfl))
    change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
      (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
        (deckV (universalSpineOldReceiver q g) t.1.1)) = _
    rw [univLiftV_deckV, uCoverPathTransport_deckV,
      ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
    change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
      (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
        (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g)))) _ = _
    rw [pi1Conj_cancel_reverse]; rfl
  have hmcorr (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) :
      chain2 (universalOldToNamedQuotient ρ q u) (universalOldMarkingCorrections q c) =
        quotientMarkingCorrections q ρ u hrho
          (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
            (singleSpineNamedReceiver ρ q u x.1, x.2)) c) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add _ _ hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
    | single x n =>
        rw [universalOldMarkingCorrections, Finsupp.linearCombination_single, map_smul,
          universalOldMarkingCorrection, hdeck, ← chain2_comp_apply, hsq2,
          Finsupp.mapDomain_single, quotientMarkingCorrections, Finsupp.linearCombination_single]
        rfl
  have hchain : quotientCorrectedRelativeChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
      chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
          universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)) := by
    rw [quotientCorrectedRelativeChain, singleFiniteSpineReference_faceChain,
      singleFiniteSpineReference_markingChain, map_sub, hmcorr]
    congr 1
    change chain2 (receivedSpineToQuotient q ρ u hrho)
      (chain2 (ReceivedTree.changeGroup (markedSpineTree q) (universalSpineWordReceiver q)
        (singleSpineNamedReceiver ρ q u)) (normalizedSpineReference q)) = _
    erw [← chain2_comp_apply, hsq1, chain2_comp_apply]
  simpa only [quotientCorrectedRelativeNerveChain, hchain] using
    universalOldToNamedQuotient_polygon_reference ρ q u
      (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
        universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q))
      (normalizedSpineReference_corrected_geometry q)
