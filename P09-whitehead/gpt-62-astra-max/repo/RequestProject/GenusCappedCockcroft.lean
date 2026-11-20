module

public import RequestProject.GenusOldAugmentationVanishing
public import RequestProject.GenusCappedSpineFox


@[expose] public section

/-! Cockcroftness of the actual capped spine, with no geometric input premise. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

/-- Collapsing the spanning tree reflects the two-cycle condition. -/
theorem cappedPresentationCycle_treeCycle
    (c : (univCover (cappedSpinePresentation q)).F →₀ ℤ)
    (hc : Comb.bdry2 _ c = 0) :
    Comb.bdry2 (cappedTreeCover q) c = 0 := by
  let T := cappedSpineTree q
  let N := relSub (cappedSpinePresentation q)
  have hN : ∀ f, SpanningTree.treeRel T f ∈ N := by
    erw [cappedSpineTree_rel]
    apply rel_mem_relSub
  have hp : SpanningTree.piE T N (Comb.bdry2 (cappedTreeCover q) c) = 0 := by
    erw [SpanningTree.piE_bdry2 (hN := hN)]
    change Finsupp.linearCombination ℤ
      (fun f => pathChain (liftPath
        (FreeGroup.toWord (SpanningTree.treeRel (cappedSpineTree q) f.2)) f.1)) c = 0; erw [(cappedSpineTree_rel q)]; exact hc
  exact SpanningTree.treeChain_eq_zero (T := T) (N := N) (hN := hN)
    (SpanningTree.support_isTree_of_piE_eq_zero (T := T) (N := N) hp)
    (Comb.bdry1_bdry2 (X := cappedTreeCover q) c)

/-- The genuine capped presentation is Cockcroft. -/
theorem cappedSpinePresentation_isCockcroft :
    _root_.FiniteChains.IsCockcroft (cappedSpinePresentation q) := by
  apply (coverCycles_cockcroft_iff (cappedSpinePresentation q)).mp
  solve_by_elim [cappedCoverCycle_total_augmentation_zero, cappedPresentationCycle_treeCycle]

end FiniteChains.Davis.Genus
