import RequestProject.ClassicalGraphContraction
import Mathlib.Topology.Homotopy.Contractible
import RequestProject.Tac


/-! A genuine continuous contraction of the disk realization of an arbitrary
spanning tree. Only each vertex's natural-number height is finite. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (T : Comb.SpanningTree (graphCx r))

def treeAttaching : BoundaryFamily {j : J // T.isTree j} (Fin 1 → ℝ) → V :=
  fun a => r ⟨a.1.val, a.2⟩

abbrev TreeSpace := DiskAttachment (treeAttaching r T)

def treeVertex (a : V) : TreeSpace r T :=
  old _ _ a

def treeUpPath (a : V) (ha : a ≠ T.root) :
    Path (treeVertex r T a) (treeVertex r T (T.parent a ha)) :=
  (graphGermPath (treeAttaching r T)
    (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)).cast
      (congrArg (treeVertex r T) (T.up_src a ha).symm) rfl

/-- Follow the finitely many chosen parent edges to the root. -/
def treeRootPath a : Path (treeVertex r T a) (treeVertex r T T.root) :=
  if ha : a = T.root then
    (Path.refl _).cast (by simp_all) rfl
  else (treeUpPath r T a ha).trans (treeRootPath (T.parent a ha))
  termination_by T.ht a
  decreasing_by
    have h := T.ht_parent ha
    omega


theorem treeRootPath_of_ne ha :
    treeRootPath r T a = (treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha)) := by
  rw [treeRootPath]
  simp_all

/-- Every retained edge is a chosen parent edge, so the actual vertex paths
have precisely the compatibility used by the cellwise contraction. -/
theorem treeRootPath_edge j :
    treeRootPath r T (graphSrc (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).trans
        (treeRootPath r T (graphTgt (treeAttaching r T) j)) ∨
    treeRootPath r T (graphTgt (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).symm.trans
        (treeRootPath r T (graphSrc (treeAttaching r T) j)) := by
  obtain ⟨a, ha, he⟩ := (T.isTree_iff j.val).mp j.property
  cases hb : (T.up a ha).2 with
  | false =>
      have hg : T.up a ha = (j.val, false) := Prod.ext he hb
      have ha' : a = graphTgt (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_false, graphTgt, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphSrc (treeAttaching r T) j := by
        simp [Comb.SpanningTree.parent, hg, Comb.germTgt_false]
        rfl
      right
      apply Path.ext
      funext t
      have h := congrArg (· t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = (graphEdgePath _ j).symm s := by
        intro s
        have hpair :
            ((⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)) = (j, false) := by
          simp_all
        exact congrArg
          (graphGermPath _ · s)
          hpair
      calc
        treeRootPath r T (graphTgt (treeAttaching r T) j) t = treeRootPath r T a t :=
          by grind
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T _)) t := h
        _ = _ := by
          simp [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (treeRootPath r T · _) hp
  | true =>
      have hg : T.up a ha = (j.val, true) := Prod.ext he hb
      have ha' : a = graphSrc (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_true, graphSrc, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphTgt (treeAttaching r T) j := by
        simp [Comb.SpanningTree.parent, hg, Comb.germTgt_true]
        rfl
      left
      apply Path.ext
      funext t
      have h := congrArg (· t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = graphEdgePath _ j s := by
        intro s
        have hpair :
            ((⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)) = (j, true) := by
          simp_all
        exact congrArg
          (graphGermPath _ · s)
          hpair
      calc
        treeRootPath r T (graphSrc (treeAttaching r T) j) t = treeRootPath r T a t :=
          by grind
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T _)) t := h
        _ = _ := by
          simp [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (treeRootPath r T · _) hp

variable [DiscreteTopology V]

/-- The actual spanning-tree disk attachment is contracted to its literal
old root vertex. The entire tree may have arbitrarily many edges. -/
def treeContraction : ContinuousMap.Homotopy (ContinuousMap.id (TreeSpace r T))
    (ContinuousMap.const (TreeSpace r T) (treeVertex r T T.root)) :=
  graphContraction (treeAttaching r T) T.root _ (treeRootPath_edge r T)



/-- The same specified collapse, with the universe-polymorphic singleton. -/
def treeHomotopyEquivPUnit : ContinuousMap.HomotopyEquiv (TreeSpace r T) PUnit where
  toFun := ContinuousMap.const _ PUnit.unit
  invFun := ContinuousMap.const _ (treeVertex r T T.root)
  left_inv := ⟨(treeContraction r T).symm⟩
  right_inv := by
    rfl
