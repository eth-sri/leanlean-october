import Mathlib.Tactic

import RequestProject.UniversalTreeGauge
import RequestProject.GenusFullCubeMarking

/-! Exact lifted path translations for the genuine capped presentation group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

variable (g : PresGroup (cappedSpinePresentation q))
variable (a : (markedSpineCx q).V)
noncomputable def rootedCappedFullVertex 
      :=
  deckV (cappedPresentationToFullCube q g)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q) a)

theorem rootedCappedFullVertex_end 
     :
    endV (rootedCappedFullVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [rootedCappedFullVertex, endV_deckV, SpanningTree.mappedTreeReference_end]

/-- Traversing any genuine spine path updates the comparison vertex by its capped-group word. -/
theorem rootedCappedFullVertex_path 
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    extendList (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) =
      rootedCappedFullVertex q
        (g * QuotientGroup.mk (SpanningTree.pathWord (markedSpineTree q) p)) b := by
  unfold rootedCappedFullVertex
  rw [extendList_deckV, SpanningTree.mappedTreeReference_path _ _ hp,
    map_mul, cappedPresentationToFullCube_mk, deckV_mul]
  rfl

/-- Comparison edges are actual edges in the full path-class universal cover. -/
noncomputable def rootedCappedFullEdge 
    (e : (markedSpineCx q).E) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).src e),
    (markedSpineToFullCube q).onE e), by
      aesop (add simp [rootedCappedFullVertex_end])⟩

end FiniteChains.Davis.Genus
