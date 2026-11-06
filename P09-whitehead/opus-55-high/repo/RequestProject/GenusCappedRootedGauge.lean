import RequestProject.UniversalTreeGauge
import RequestProject.GenusFullCubeMarking
import RequestProject.Tac
noncomputable section


/-! Exact lifted path translations for the genuine capped presentation group. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def rootedCappedFullVertex (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :=
  deckV (cappedPresentationToFullCube q g)
    (SpanningTree.mappedTreeReference _ _ a)

theorem rootedCappedFullVertex_end g
    a :
    endV (rootedCappedFullVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [rootedCappedFullVertex, endV_deckV, SpanningTree.mappedTreeReference_end]

/-- Traversing any genuine spine path updates the comparison vertex by its capped-group word. -/
theorem rootedCappedFullVertex_path g
    {a b} {p}
    (hp : IsPathX (markedSpineCx q) p a b) :
    extendList (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) =
      rootedCappedFullVertex q
        (g * QuotientGroup.mk (SpanningTree.pathWord (markedSpineTree q) p)) b := by
  unfold rootedCappedFullVertex
  rw [extendList_deckV, SpanningTree.mappedTreeReference_path _ _ hp,
    map_mul, cappedPresentationToFullCube_mk, deckV_mul]
  rfl

/-- Comparison edges are actual edges in the full path-class universal cover. -/
def rootedCappedFullEdge (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).src e),
    (markedSpineToFullCube q).onE e), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).src_onE]⟩
