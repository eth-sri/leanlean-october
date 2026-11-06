import Mathlib.Tactic

import RequestProject.ClassicalSpanningTreeContraction
import RequestProject.DiskAttachmentPartition
import RequestProject.DiskFamilyHomotopyBaseChange

/-! Collapse an actual arbitrary spanning tree in a disk graph. The forward
map collapses all vertices and tree disks, and retains every other disk
with its original interval parameter. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable (A : Type)
def roseAttaching  : C(BoundaryFamily A (Fin 1 → ℝ), PUnit) :=
  ContinuousMap.const _ PUnit.unit

abbrev Rose  := DiskAttachment (roseAttaching A)

def roseVertex   :=
  old (roseAttaching A) (boundaryFamilyInclusion A _) PUnit.unit

variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def nonTreeAttaching : C(BoundaryFamily {j : J // ¬T.isTree j} (Fin 1 → ℝ), TreeSpace r T) :=
  ⟨partitionRestAttaching r T.isTree, partitionRestAttaching_continuous r T.isTree hr⟩

/-- The concrete graph-to-rose equivalence. Its only combinatorial input is
the genuine spanning tree, whose contraction is constructed above. -/
def graphRoseHomotopyEquiv  :=
  (diskAttachmentPartitionHomeomorph r T.isTree).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T) (treeHomotopyEquivPUnit r T))

@[simp] theorem graphRoseHomotopyEquiv_old (v : V) :
    graphRoseHomotopyEquiv r hr T (old r (boundaryFamilyInclusion J _) v) =
      roseVertex {j : J // ¬T.isTree j} := rfl

@[simp] theorem graphRoseHomotopyEquiv_treeCell
    (d : DiskFamily {j : J // T.isTree j} (Fin 1 → ℝ)) :
    graphRoseHomotopyEquiv r hr T
      (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩) =
      roseVertex {j : J // ¬T.isTree j} := by
  change diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T)
      (treeHomotopyEquivPUnit r T)
      (partitionRegroup r T.isTree (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩)) = _
  rw [partitionRegroup_firstCell r T.isTree d]
  exact diskAttachmentBaseChangeHomotopyEquiv_old (nonTreeAttaching r hr T)
    (treeHomotopyEquivPUnit r T)
    (cell (partitionFirstAttaching r T.isTree)
      (boundaryFamilyInclusion {j : J // T.isTree j} (Fin 1 → ℝ)) d)

@[simp] theorem graphRoseHomotopyEquiv_nonTreeCell
    (d : DiskFamily {j : J // ¬T.isTree j} (Fin 1 → ℝ)) :
    graphRoseHomotopyEquiv r hr T
      (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩) =
      cell (roseAttaching {j : J // ¬T.isTree j})
        (boundaryFamilyInclusion {j : J // ¬T.isTree j} _) d := by
  change diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T)
      (treeHomotopyEquivPUnit r T)
      (partitionRegroup r T.isTree (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩)) = _
  rw [partitionRegroup_restCell r T.isTree d]
  exact diskAttachmentBaseChangeHomotopyEquiv_cell (nonTreeAttaching r hr T)
    (treeHomotopyEquivPUnit r T) d

theorem graphRoseHomotopyEquiv_treePath (j : {j : J // T.isTree j}) (t : I) :
    graphRoseHomotopyEquiv r hr T (graphEdgePath r j.val t) =
      roseVertex {j : J // ¬T.isTree j} :=
  graphRoseHomotopyEquiv_treeCell r hr T ⟨j, graphDiskHomeomorph t⟩

end FiniteChains.ClassicalGraphModel
