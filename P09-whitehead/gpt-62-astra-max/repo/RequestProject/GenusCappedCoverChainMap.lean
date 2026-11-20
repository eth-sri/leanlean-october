module

public import RequestProject.GenusCappedLiftedPaths
public import RequestProject.GenusFullCubeCoverFillings
public import RequestProject.DeckChainTransport
public import RequestProject.DavisUniversalThree

@[expose] public section

/-! The constructed two-chain comparison from the genuine capped tree cover. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}
theorem pathChain_map_edges (f : X.E → Y.E) (p : List (X.E × Bool)) :
    pathChain (p.map (fun eb => (f eb.1, eb.2))) = Finsupp.mapDomain f (pathChain p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp [hb]
      · have hn : Finsupp.mapDomain f (-Finsupp.single e.1 (1 : ℤ)) =
            -Finsupp.mapDomain f (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ f).map_neg (Finsupp.single e.1 (1 : ℤ))
        simp_all
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

abbrev rootedFullCover := uCover (orderCx (QCube (cmpRel (GenusVertex q))))
  ((markedSpineToFullCube q).onV (markedSpineTree q).root)
abbrev cappedTreeCover := SpanningTree.treeCover (cappedSpineTree q)
  (relSub (cappedSpinePresentation q)) (by
    simp_all [cappedSpineTree_rel, rel_mem_relSub])

def rootedOldFace (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) : (rootedFullCover q).F :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).base f),
    (markedSpineToFullCube q).onF f), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).base_onF]⟩

def rootedCoverChain1 :
    ((cappedTreeCover q).E →₀ ℤ) →ₗ[ℤ] ((rootedFullCover q).E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun ge => rootedCappedFullEdge q ge.1 ge.2)

theorem rootedOldFace_boundary (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) :
    Comb.bdry2 _ (Finsupp.single (rootedOldFace q g f) 1) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inl f) 1)) := by
  rw [bdry2_single, one_smul, bdry2_single, one_smul]
  change pathChain (uLiftPath ((orderCx (QCube (cmpRel (GenusVertex q)))).att
    ((markedSpineToFullCube q).onF f))
    (rootedCappedFullVertex q g ((markedSpineCx q).base f))) =
      Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
        (pathChain (SpanningTree.liftK (cappedSpineTree q)
          (relSub (cappedSpinePresentation q)) ((markedSpineCx q).att f) g))
  rw [(markedSpineToFullCube q).att_onF]
  have hp := rootedCapped_liftPath q g ((markedSpineCx q).att_isLoop f)
  simp only [mapPath] at hp; rw [← hp]; exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
    (fun ge => rootedCappedFullEdge q ge.1 ge.2) _

def rootedBaseCapFilling (x : Fin q × Bool) :=
  fullCubeCoverCapChain q x
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q))
    (SpanningTree.mappedTreeReference_end _ _ _)

variable (g : PresGroup (cappedSpinePresentation q)) (x : Fin q × Bool)

def rootedCapFilling :=
  (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).faceChains
    (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x)

theorem rootedCapFilling_boundary :
    Comb.bdry2 _ (rootedCapFilling q g x) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inr x) 1)) := by
  have hb := fullCubeCoverCapChain_boundary q x
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q)) (SpanningTree.mappedTreeReference_end _ _ _)
  have ht := (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).transport_filling
    (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x) _ hb
  have he := uLiftPath_deckV (cappedPresentationToFullCube q g)
    (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q)) ((markedSpineToFullCube q).onV (markedSpineBase q))
    (by grind [SpanningTree.mappedTreeReference_end, isPath_mapPath])
  change Comb.bdry2 _ (rootedCapFilling q g x) = pathChain
    ((uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
      (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
        (markedSpineBase q))).map
      (fun Eb => (deckE (cappedPresentationToFullCube q g) Eb.1, Eb.2))) at ht
  rw [← he] at ht
  rw [ht, bdry2_single, one_smul]
  change pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
    (rootedCappedFullVertex q g (markedSpineBase q))) =
      Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
        (pathChain (SpanningTree.liftK (cappedSpineTree q)
          (relSub (cappedSpinePresentation q)) (markedSpineLoop q x).1 g))
  rw [← rootedCapped_liftPath q g (markedSpineLoop q x).2]
  exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
    (fun ge => rootedCappedFullEdge q ge.1 ge.2) _

def rootedFaceComparison (gf : (cappedTreeCover q).F) :
    (rootedFullCover q).F →₀ ℤ :=
  match gf.2 with
  | .inl f => Finsupp.single (rootedOldFace q gf.1 f) 1
  | .inr x => rootedCapFilling q gf.1 x

def rootedCoverChain2 :=
  Finsupp.linearCombination ℤ (rootedFaceComparison q)

variable (c : (cappedTreeCover q).F →₀ ℤ)

/-- The constructed comparison commutes with the boundary on every actual cover two-chain. -/
theorem rootedCoverChain2_boundary :
    Comb.bdry2 _ (rootedCoverChain2 q c) = rootedCoverChain1 q (Comb.bdry2 _ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single gf n =>
      have hb : Comb.bdry2 _ (rootedFaceComparison q gf) =
          rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single gf 1)) := by
        obtain ⟨g, f | x⟩ := gf
        · apply rootedOldFace_boundary
        · apply rootedCapFilling_boundary
      rw [rootedCoverChain2, Finsupp.linearCombination_single, map_smul, hb] <;> simp_all

/-- Every genuine capped-cover cycle has a degree-three filling after this comparison. -/
theorem rootedCoverCycle_fullCube_filling
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : UOrdTet (QCube (cmpRel (GenusVertex q)))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) →₀ ℤ,
      uOrdBoundary3 y = rootedCoverChain2 q c := by
  apply exists_universal_bdry3_of_cycle_qCube
  rw [rootedCoverChain2_boundary, hc, map_zero]

end FiniteChains.Davis.Genus
