import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.OrderTriangleBoundaryWords
import RequestProject.ClassicalGraphTreeBoundaryWords
import RequestProject.ClassicalRoseWordNaturality
import RequestProject.ClassicalRoseWordReduction
import RequestProject.PresCircleWordParametrization
import RequestProject.PresCanonicalWords

/-! The canonical presentation of a strict order complex is an actual
homotopy model of its realization. The prescribed spanning tree is
transported to the literal interval graph without changing edge labels.
Pending the final Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology ContinuousMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel PresModel SpanningTree
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

local instance : DiscreteTopology (Vertices P) :=
  ClassicalCW.zeroSkeleton_discrete (X := orderNerveRealization P)

theorem graph_germSrc (g : StrictOrdEdge P × Bool) :
    germSrc (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germSrc (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  aesop (add simp [germSrc, graphAttaching_source, graphAttaching_target])

theorem graph_germTgt (g : StrictOrdEdge P × Bool) :
    germTgt (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germTgt (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  aesop (add simp [germTgt, graphAttaching_source, graphAttaching_target])

variable (T : SpanningTree (strictOrderCx P))

/-- Only the vertex names change. In particular the non-tree edge type
is definitionally the prescribed type `NonTree T`. -/
def graphTree : SpanningTree (graphCx (graphAttaching P)) where
  root := vertexEquiv P T.root
  ht v := T.ht ((vertexEquiv P).symm v)
  isTree := T.isTree
  up v hv := T.up ((vertexEquiv P).symm v) (by
    grind)
  ht_root := by classical simp_all [FiniteChains.Comb.SpanningTree.ht_root]
  ht_eq_zero := by
    intro v hv
    simpa [Equiv.apply_symm_apply] using
      congrArg (vertexEquiv P) (T.ht_eq_zero _ hv)
  up_src := by
    intro v hv
    erw [graph_germSrc, T.up_src, Equiv.apply_symm_apply]
  up_ht := by
    intro v hv
    erw [graph_germTgt, Equiv.symm_apply_apply]
    exact T.up_ht _ _
  isTree_iff := by
    intro e
    constructor
    · intro he
      obtain ⟨v, hv, he⟩ := (T.isTree_iff e).mp he
      refine ⟨vertexEquiv P v, (fun h => hv ((vertexEquiv P).injective h)), ?_⟩
      simpa only [Equiv.symm_apply_apply] using he
    · classical aesop (add simp [FiniteChains.Comb.orderNerveRealization_t2Space, FiniteChains.Comb.SpanningTree.isTree_iff, vertexEquiv])



def collapsedWords (t : StrictOrdTri P)  :=
  (words P t).eraseTree (graphAttaching P) (graphTree P T)

theorem collapsedWords_mk (t : StrictOrdTri P) :
    FreeGroup.mk (collapsedWords P T t).loopWord = treeRel T t := by
  solve_by_elim [FiniteChains.ClassicalGraphModel.BoundaryWords.eraseTree_mk]

def oneSkeletonRoseEquiv  :=
  (graphHomeomorph P).symm.toHomotopyEquiv.trans
    (graphRoseHomotopyEquiv (graphAttaching P) (graphAttaching P).continuous (graphTree P T))

def collapsedAttaching  :=
  (oneSkeletonRoseEquiv P T).toFun.comp (triangleAttaching P)



abbrev collapsedCellBoundary_homotopic_words (t : StrictOrdTri P)  :=
  have H :=
    ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl
        (FiniteChains.ClassicalGraphModel.graphRoseHomotopyEquiv
            (⇑(FiniteChains.Comb.OrderEdgeAttachment.graphAttaching P))
            (ContinuousMap.continuous (FiniteChains.Comb.OrderEdgeAttachment.graphAttaching P))
            (FiniteChains.Comb.OrderTriangleWords.graphTree P T)).toFun)
      (FiniteChains.Comb.OrderTriangleWords.graphBoundary_homotopic_words P t);
  ContinuousMap.Homotopic.trans H
    (FiniteChains.ClassicalGraphModel.BoundaryWords.collapse_homotopic_eraseTree
      (⇑(FiniteChains.Comb.OrderEdgeAttachment.graphAttaching P))
      (ContinuousMap.continuous (FiniteChains.Comb.OrderEdgeAttachment.graphAttaching P))
      (FiniteChains.Comb.OrderTriangleWords.graphTree P T) (FiniteChains.Comb.OrderTriangleWords.words P t))

variable (a : NonTree T)

abbrev collapsedCellBoundary_homotopic_canonical (t : StrictOrdTri P)  :=
  have he :=
    Eq.trans (FiniteChains.Comb.OrderTriangleWords.collapsedWords_mk P T t)
      (Eq.symm (FiniteChains.PresModel.mk_presCanonicalWords T.treeRel a t));
  ContinuousMap.Homotopic.trans (FiniteChains.Comb.OrderTriangleWords.collapsedCellBoundary_homotopic_words P T t)
    (ContinuousMap.Homotopic.trans
      (FiniteChains.PresModel.boundaryWords_homotopic_classicalWord
        (FiniteChains.Comb.OrderTriangleWords.collapsedWords P T t))
      (ContinuousMap.Homotopic.trans (FiniteChains.PresModel.classicalRoseWordBoundary_homotopic_of_mk_eq he)
        (ContinuousMap.Homotopic.symm
          (FiniteChains.PresModel.classicalPresWordAttaching_homotopic_read
            (FiniteChains.PresModel.presCanonicalWords T.treeRel a) t
            (FiniteChains.PresModel.presCanonicalWords_ne_nil T.treeRel a)))))

def collapsedAttachingCanonicalHomotopy :
    (collapsedAttaching P T).Homotopy
      (classicalPresWordAttaching (presCanonicalWords (treeRel T) a)
        (presCanonicalWords_ne_nil (treeRel T) a)) := by
  let H (t : StrictOrdTri P) := Classical.choice
    (collapsedCellBoundary_homotopic_canonical P T a t)
  let F : C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (NonTree T))) :=
    ⟨fun z => ((H z.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry z.2,
      continuous_sigma (fun t =>
        ((H t).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun z => (H z.1).apply_zero z.2
    map_one_left := fun z => (H z.1).apply_one z.2 }

/-- The comparison uses the actual CW attaching maps of every triangle,
not a homology or fundamental-group surrogate for a homotopy equivalence. -/
def canonicalTreeDiskRealizationEquiv [Nonempty P] [(nerve P).HasDimensionLE 2]
    (hP : IsConnected (orderCx P)) :
    ClassicalPresWordDisks (presCanonicalWords (treeRel T) a)
      (presCanonicalWords_ne_nil (treeRel T) a) ≃ₕ orderNerveRealization P :=
  (((triangleAttachmentRealizationHomeomorph P hP).symm.toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (triangleAttaching P)
      (oneSkeletonRoseEquiv P T))).trans
    (diskAttachingHomotopyEquiv (collapsedAttaching P T)
      (classicalPresWordAttaching (presCanonicalWords (treeRel T) a)
        (presCanonicalWords_ne_nil (treeRel T) a))
      (collapsedAttachingCanonicalHomotopy P T a))).symm

end FiniteChains.Comb.OrderTriangleWords
