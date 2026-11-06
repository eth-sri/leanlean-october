import RequestProject.GenusOldAugmentationVanishing
import RequestProject.GenusCappedSpineFox
import RequestProject.TreeCoverAcyclic
import RequestProject.Tac


/-! Cockcroftness of the actual capped spine, with no geometric input premise. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

/-- Collapsing the spanning tree reflects the two-cycle condition. -/
theorem cappedPresentationCycle_treeCycle
    c
    (hc : Comb.bdry2 (univCover (cappedSpinePresentation q)) c = 0) :
    Comb.bdry2 (cappedTreeCover q) c = 0 := by
  let T := cappedSpineTree q
  let N := relSub (cappedSpinePresentation q)
  have hN : ∀ f, T.treeRel f ∈ N := by
    intro f
    rwd [cappedSpineTree_rel]
    exact rel_mem_relSub _ f
  have hp : T.piE N (Comb.bdry2 (cappedTreeCover q) c) = 0 := by
    rwd [SpanningTree.piE_bdry2 (hN := hN)]
    have hrel :=
      cappedSpineTree_rel q
    change Finsupp.linearCombination ℤ
      (fun f => pathChain (liftPath
        (FreeGroup.toWord (SpanningTree.treeRel (cappedSpineTree q) f.2)) f.1)) c = 0
    aesop
  exact SpanningTree.treeChain_eq_zero (T := T) (N := N) (hN := hN)
    (SpanningTree.support_isTree_of_piE_eq_zero (T := T) (N := N) hp)
    (Comb.bdry1_bdry2 (X := cappedTreeCover q) c)

/-- The genuine capped presentation is Cockcroft. -/
theorem cappedSpinePresentation_isCockcroft :
    _root_.FiniteChains.IsCockcroft (cappedSpinePresentation q) := by
  apply (coverCycles_cockcroft_iff _).mp
  intro c hc
  exact cappedCoverCycle_total_augmentation_zero q c
    (cappedPresentationCycle_treeCycle q c hc)
