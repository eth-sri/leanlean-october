module

public import RequestProject.Oriented
public import RequestProject.UniversalTreeGauge
public import RequestProject.GenusFullCubeMarking

@[expose] public section

backwardOptions



/-! Exact lifted path translations for the genuine capped presentation group. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def rootedCappedFullVertex (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    UV (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  deckV (cappedPresentationToFullCube q g)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q) a)

theorem rootedCappedFullVertex_end (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    endV (rootedCappedFullVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [rootedCappedFullVertex, endV_deckV, SpanningTree.mappedTreeReference_end]

/-- Traversing any genuine spine path updates the comparison vertex by its capped-group word. -/
theorem rootedCappedFullVertex_path (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : FiniteChains.Comb.Oriented (markedSpineCx q).E}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    extendList (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) =
      rootedCappedFullVertex q
        (g * QuotientGroup.mk (SpanningTree.pathWord (markedSpineTree q) p)) b := by
  unfold rootedCappedFullVertex
  rw [extendList_deckV, SpanningTree.mappedTreeReference_path _ _ hp,
    map_mul, cappedPresentationToFullCube_mk, deckV_mul]
  rfl

/-- Comparison edges are actual edges in the full path-class universal cover. -/
noncomputable def rootedCappedFullEdge (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).src e),
    (markedSpineToFullCube q).onE e), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).src_onE]⟩

end FiniteChains.Davis.Genus
